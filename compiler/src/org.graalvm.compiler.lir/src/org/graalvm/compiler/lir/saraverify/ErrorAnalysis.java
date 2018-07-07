package org.graalvm.compiler.lir.saraverify;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.graalvm.compiler.core.common.cfg.AbstractBlockBase;
import org.graalvm.compiler.core.common.cfg.BlockMap;
import org.graalvm.compiler.debug.DebugContext;
import org.graalvm.compiler.debug.DebugContext.Scope;
import org.graalvm.compiler.debug.Indent;
import org.graalvm.compiler.lir.InstructionValueConsumer;
import org.graalvm.compiler.lir.LIR;
import org.graalvm.compiler.lir.LIRInstruction;
import org.graalvm.compiler.lir.LIRInstruction.OperandFlag;
import org.graalvm.compiler.lir.LIRInstruction.OperandMode;
import org.graalvm.compiler.lir.LIRValueUtil;
import org.graalvm.compiler.lir.saraverify.DefAnalysis.DefAnalysisNonCopyValueConsumer;
import org.graalvm.compiler.lir.saraverify.DefAnalysis.DefAnalysisTempValueConsumer;
import org.graalvm.compiler.lir.saraverify.DefAnalysisInfo.Triple;
import org.graalvm.compiler.lir.saraverify.DuSequenceAnalysis.DummyConstDef;
import org.graalvm.compiler.lir.saraverify.DuSequenceAnalysis.DummyRegDef;

import jdk.vm.ci.code.Register;
import jdk.vm.ci.code.RegisterArray;
import jdk.vm.ci.code.ValueUtil;
import jdk.vm.ci.meta.Constant;
import jdk.vm.ci.meta.Value;
import jdk.vm.ci.meta.ValueKind;

public class ErrorAnalysis {

    protected final static String DEBUG_SCOPE = "SARAVerifyErrorAnalysis";

    public static void analyse(LIR lir, DefAnalysisResult defAnalysisResult, Map<Node, DuSequenceWeb> mapping, Map<Register, DummyRegDef> dummyRegDefs, Map<Constant, DummyConstDef> dummyConstDefs,
                    RegisterArray callerSaveRegisters, BlockMap<List<Value>> blockPhiInValues, BlockMap<List<Value>> blockPhiOutValues) {
        DebugContext debugContext = lir.getDebug();
        // log information
        try (Indent i = debugContext.indent(); Scope s = debugContext.scope(DEBUG_SCOPE)) {
            debugContext.log(3, "starting error analysis ...");
        }

        Map<AbstractBlockBase<?>, DefAnalysisInfo> blockInfos = defAnalysisResult.getBlockSets();

        // create a list of register values with value kind illegal of caller saved registers
        List<Value> callerSaveRegisterValues = callerSaveRegisters.asList() //
                        .stream().map(register -> register.asValue(ValueKind.Illegal)).collect(Collectors.toList());

        List<Value> tempValues = new ArrayList<>();

        AbstractBlockBase<?>[] blocks = lir.getControlFlowGraph().getBlocks();
        for (AbstractBlockBase<?> block : blocks) {

            DefAnalysisInfo defAnalysisInfo;
            if (block.getId() == 0) {
                defAnalysisInfo = new DefAnalysisInfo();
                DefAnalysis.initializeDefAnalysisInfo(mapping, dummyRegDefs, dummyConstDefs, defAnalysisInfo);
            } else {
                defAnalysisInfo = DefAnalysis.mergeDefAnalysisInfo(lir, blockInfos, block, mapping, blockPhiInValues, blockPhiOutValues);
            }

            ErrorAnalysisValueConsumer errorAnalysisValueConsumer = new ErrorAnalysisValueConsumer(mapping, defAnalysisInfo);

            DefAnalysisNonCopyValueConsumer nonCopyValueConsumer = new DefAnalysisNonCopyValueConsumer(defAnalysisInfo, mapping);
            DefAnalysisTempValueConsumer tempValueConsumer = new DefAnalysisTempValueConsumer(tempValues);

            ArrayList<LIRInstruction> instructions = lir.getLIRforBlock(block);
            for (LIRInstruction instruction : instructions) {
                errorAnalysisValueConsumer.useOperandPosition = 0;

                if (!instruction.isMoveOp()) {
                    // non copy instruction
                    // error analysis
                    SARAVerifyUtil.visitValues(instruction, null, errorAnalysisValueConsumer);
                }

                // compute local flow
                DefAnalysis.computeLocalFlowInstruction(defAnalysisInfo, callerSaveRegisterValues, tempValues, nonCopyValueConsumer, tempValueConsumer, instruction);
            }
        }

        try (Indent i = debugContext.indent(); Scope s = debugContext.scope(DEBUG_SCOPE)) {
            debugContext.log(3, "error analysis done");
        }
    }

    private static void useCheck(Value value, int useOperandPosition, LIRInstruction instruction, Map<Node, DuSequenceWeb> mapping, DefAnalysisInfo defAnalysisInfo) {

        UseNode useNode = new UseNode(value, instruction, useOperandPosition);
        DuSequenceWeb mappedWeb = mapping.get(useNode);

        assert mappedWeb != null : "no mapping found for usage";

        List<Triple> locationTriples = defAnalysisInfo.getLocationTriples(mappedWeb);
        Value location = SARAVerifyUtil.getValueIllegalValueKind(value);

        StringBuilder stringBuilder = new StringBuilder();

        if (locationTriples.stream().anyMatch(triple -> triple.getLocation().equals(location))) {
            // mapped value is in assumed location

            Triple staleTriple = defAnalysisInfo.getStaleTriple(location, mappedWeb);
            if (staleTriple != null) {
                // value is stale
                appendStaleErrorMessage(value, instruction, stringBuilder, staleTriple);
            }
            // mapped value is in assumed location and not stale ==> correct usage
        } else {
            // mapped value is not in assumed location
            List<Triple> otherLocationTriples = locationTriples.stream()       //
                            .filter(triple -> defAnalysisInfo.getStaleTriple(triple.getLocation(), triple.getValue()) == null)  //
                            .collect(Collectors.toList());

            if (otherLocationTriples.size() == 0) {
                // mapped value is evicted
                List<Triple> evictedTriples = defAnalysisInfo.getEvictedTriples(mappedWeb);

                appendEvictedErrorMessage(value, instruction, stringBuilder, evictedTriples);
            } else {
                // mapped value is in other location
                appendWrongOperandErrorMessage(value, instruction, stringBuilder, otherLocationTriples);
            }
        }

        if (stringBuilder.length() > 0) {
            throw SARAVerifyError.shouldNotReachHere(stringBuilder.toString());
        }
    }

    private static void appendWrongOperandErrorMessage(Value value, LIRInstruction instruction, StringBuilder stringBuilder, List<Triple> otherLocationTriples) {
        stringBuilder.append("instruction ");
        stringBuilder.append(instruction.id());
        stringBuilder.append(" ");
        stringBuilder.append(instruction);
        stringBuilder.append(" uses wrong operand value ");
        stringBuilder.append(value);
        stringBuilder.append("\n");

        for (Triple triple : otherLocationTriples) {
            stringBuilder.append("value is in location ");
            stringBuilder.append(triple.getLocation());
            stringBuilder.append("\n");
        }
    }

    private static void appendStaleErrorMessage(Value value, LIRInstruction instruction, StringBuilder stringBuilder, Triple staleTriple) {
        stringBuilder.append("instruction ");
        stringBuilder.append(instruction.id());
        stringBuilder.append(" ");
        stringBuilder.append(instruction);
        stringBuilder.append(" uses stale value ");
        stringBuilder.append(value);
        stringBuilder.append("\n");
        stringBuilder.append("The value become stale along the following sequence:\n");
        appendInstructionSequence(staleTriple.getInstructionSequence(), stringBuilder);
    }

    private static void appendEvictedErrorMessage(Value value, LIRInstruction instruction, StringBuilder stringBuilder, List<Triple> evictedTriples) {
        stringBuilder.append("instruction ");
        stringBuilder.append(instruction.id());
        stringBuilder.append(" ");
        stringBuilder.append(instruction);
        stringBuilder.append(" uses evicted value ");
        stringBuilder.append(value);
        stringBuilder.append("\n");

        for (Triple triple : evictedTriples) {
            stringBuilder.append("value evicted from location ");
            stringBuilder.append(triple.getLocation());
            stringBuilder.append(" in ");
            appendInstructionSequence(triple.getInstructionSequence(), stringBuilder);
            stringBuilder.append("\n");
        }
    }

    private static void appendInstructionSequence(ArrayList<LIRInstruction> instructionSequence, StringBuilder stringBuilder) {
        for (int i = 0; i < instructionSequence.size(); i++) {
            if (i > 0) {
                stringBuilder.append(", ");
            }

            LIRInstruction instruction = instructionSequence.get(i);
            stringBuilder.append(instruction.id());
            stringBuilder.append(" ");
            stringBuilder.append(instruction);
        }
    }

    private static class ErrorAnalysisValueConsumer implements InstructionValueConsumer {

        private final Map<Node, DuSequenceWeb> mapping;
        private final DefAnalysisInfo defAnalysisInfo;
        private int useOperandPosition;

        public ErrorAnalysisValueConsumer(Map<Node, DuSequenceWeb> mapping, DefAnalysisInfo defAnalysisInfo) {
            this.mapping = mapping;
            this.defAnalysisInfo = defAnalysisInfo;
            useOperandPosition = 0;
        }

        @Override
        public void visitValue(LIRInstruction instruction, Value value, OperandMode mode, EnumSet<OperandFlag> flags) {
            if (flags.contains(OperandFlag.UNINITIALIZED) || ValueUtil.isIllegal(value) || LIRValueUtil.isConstantValue(value)) {
                useOperandPosition++;
                return;
            }

            useCheck(value, useOperandPosition, instruction, mapping, defAnalysisInfo);
            useOperandPosition++;
        }
    }

}
