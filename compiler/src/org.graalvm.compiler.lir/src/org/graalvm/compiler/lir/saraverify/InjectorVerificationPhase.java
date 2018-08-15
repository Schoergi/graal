package org.graalvm.compiler.lir.saraverify;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;

import org.graalvm.compiler.core.common.PermanentBailoutException;
import org.graalvm.compiler.core.common.cfg.AbstractBlockBase;
import org.graalvm.compiler.core.common.cfg.AbstractControlFlowGraph;
import org.graalvm.compiler.core.common.cfg.BlockMap;
import org.graalvm.compiler.debug.CounterKey;
import org.graalvm.compiler.debug.DebugContext;
import org.graalvm.compiler.debug.DebugContext.Scope;
import org.graalvm.compiler.debug.GraalError;
import org.graalvm.compiler.debug.Indent;
import org.graalvm.compiler.lir.InstructionValueProcedure;
import org.graalvm.compiler.lir.LIR;
import org.graalvm.compiler.lir.LIRInstruction;
import org.graalvm.compiler.lir.LIRInstruction.OperandFlag;
import org.graalvm.compiler.lir.LIRInstruction.OperandMode;
import org.graalvm.compiler.lir.LIRValueUtil;
import org.graalvm.compiler.lir.StandardOp.LabelOp;
import org.graalvm.compiler.lir.StandardOp.ValueMoveOp;
import org.graalvm.compiler.lir.gen.LIRGenerationResult;
import org.graalvm.compiler.lir.phases.AllocationPhase.AllocationContext;
import org.graalvm.compiler.lir.phases.LIRPhase;
import org.graalvm.compiler.options.Option;
import org.graalvm.compiler.options.OptionKey;
import org.graalvm.compiler.options.OptionType;

import jdk.vm.ci.code.Register;
import jdk.vm.ci.code.RegisterValue;
import jdk.vm.ci.code.TargetDescription;
import jdk.vm.ci.code.ValueUtil;
import jdk.vm.ci.meta.AllocatableValue;
import jdk.vm.ci.meta.Value;

public class InjectorVerificationPhase extends LIRPhase<AllocationContext> {

    private final static String DEBUG_SCOPE = "SARAVerifyInjectorVerification";
    private final static int ERROR_COUNT = 5;

    private static int wrongRegisterAssignmentCount;
    private static int wrongRegisterUseCount;

    private static final CounterKey testsInjectedErrors = DebugContext.counter("SARAVerifyInjector[tests with injected errors]");
    private static final CounterKey testsDetectedInjectedErrors = DebugContext.counter("SARAVerifyInjector[tests where injected errors were detected]");
    private static final CounterKey executedTests = DebugContext.counter("SARAVerifyInjector[total number of executed tests]");

    public static class Options {
        // @formatter:off
        @Option(help = "Enable fault injector for the static analysis register allocation verification.", type = OptionType.Debug)
        public static final OptionKey<Boolean> SARAVerifyInjector = new OptionKey<>(false);
        // @formatter:on
    }

    @Override
    protected void run(TargetDescription target, LIRGenerationResult lirGenRes, AllocationContext context) {
        LIR lir = lirGenRes.getLIR();
        DebugContext debugContext = lir.getDebug();

        boolean injectedMissingSpillLoadErrors = injectMissingSpillLoadErrors(lir);
        boolean injectedWrongRegisterAssignmentErrors = injectWrongRegisterAssignmentErrors(lirGenRes, context);
        boolean injectedWrongRegisterUseErrors = injectWrongRegisterUseErrors(lirGenRes, context);

        boolean injectedErrors = injectedMissingSpillLoadErrors || injectedWrongRegisterAssignmentErrors || injectedWrongRegisterUseErrors;

        executedTests.increment(debugContext);

        // log that no errors were injected
        if (!injectedErrors) {
            try (Indent i = debugContext.indent(); Scope s = debugContext.scope(DEBUG_SCOPE)) {
                debugContext.log(3, "%s", "No injected errors.");
            }
        } else {
            testsInjectedErrors.increment(debugContext);
        }

        try {
            VerificationPhase.runVerification(lirGenRes, context);
            if (injectedErrors) {
                GraalError.shouldNotReachHere("Injected errors were not detected.");
            }
        } catch (SARAVerifyError error) {
            // sara verify error occured
            if (!injectedErrors) {
                GraalError.shouldNotReachHere("SARAVerify error without having injected errors.");
            } else {
                testsDetectedInjectedErrors.increment(debugContext);
            }
        }

        throw new PermanentBailoutException("SARAVerify Injector test");
    }

    private static boolean injectMissingSpillLoadErrors(LIR lir) {
        AbstractControlFlowGraph<?> controlFlowGraph = lir.getControlFlowGraph();
        AbstractBlockBase<?>[] blocks = controlFlowGraph.getBlocks();

        if (blocks.length == 1) {
            return false;
        }

        int missingSpillCount = 0;
        int missingLoadCount = 0;

        BlockMap<ArrayList<LIRInstruction>> missingSpillsLoadsMap = new BlockMap<>(controlFlowGraph);

        for (AbstractBlockBase<?> block : blocks) {
            ArrayList<LIRInstruction> instructions = lir.getLIRforBlock(block);
            ArrayList<LIRInstruction> missingSpillsLoads = new ArrayList<>();

            for (LIRInstruction instruction : instructions) {
                // inject missing spill, load
                if (instruction.isValueMoveOp()) {
                    ValueMoveOp valueMoveOp = (ValueMoveOp) instruction;
                    AllocatableValue result = valueMoveOp.getResult();
                    AllocatableValue input = valueMoveOp.getInput();

                    if (LIRValueUtil.isStackSlotValue(result) && missingSpillCount < ERROR_COUNT) {
                        // inject missing spill
                        missingSpillsLoads.add(instruction);
                        missingSpillCount++;
                    } else if (LIRValueUtil.isStackSlotValue(input) && missingLoadCount < ERROR_COUNT) {
                        // inject missing load
                        missingSpillsLoads.add(instruction);
                        missingLoadCount++;
                    }
                }
            }

            missingSpillsLoadsMap.put(block, missingSpillsLoads);
        }

        // remove instructions to inject missing spills and loads
        for (AbstractBlockBase<?> block : blocks) {
            ArrayList<LIRInstruction> missingSpillLoads = missingSpillsLoadsMap.get(block);

            if (missingSpillLoads != null) {
                ArrayList<LIRInstruction> instructions = lir.getLIRforBlock(block);
                instructions.removeAll(missingSpillLoads);
            }
        }

        return missingSpillCount != 0 || missingLoadCount != 0;
    }

    private static boolean injectWrongRegisterAssignmentErrors(LIRGenerationResult lirGenRes, AllocationContext context) {
        LIR lir = lirGenRes.getLIR();
        AbstractBlockBase<?>[] blocks = lir.getControlFlowGraph().getBlocks();
        Random random = new Random();
        wrongRegisterAssignmentCount = 0;

        for (AbstractBlockBase<?> block : blocks) {
            ArrayList<LIRInstruction> instructions = lir.getLIRforBlock(block);

            for (LIRInstruction instruction : instructions) {

                if (!(instruction instanceof LabelOp) && wrongRegisterAssignmentCount < ERROR_COUNT) {
                    instruction.forEachOutput(new InstructionValueProcedure() {

                        @Override
                        public Value doValue(LIRInstruction inst, Value value, OperandMode mode, EnumSet<OperandFlag> flags) {
                            if (ValueUtil.isRegister(value)) {
                                RegisterValue register = ValueUtil.asRegisterValue(value);

                                // get all allocatable registers, that have the same register
                                // category as the correct register
                                List<Register> filteredRegisters = getFilteredAllocatableRegistersSamePlatformKind(context, value);

                                if (filteredRegisters.size() == 0) {
                                    return value;
                                }
                                instruction.setComment(lirGenRes, "injected wrong register assignment error");

                                wrongRegisterAssignmentCount++;
                                int index = random.nextInt(filteredRegisters.size());
                                return filteredRegisters.get(index).asValue(register.getValueKind());
                            }

                            return value;
                        }
                    });
                }
            }
        }

        return wrongRegisterAssignmentCount != 0;
    }

    private static boolean injectWrongRegisterUseErrors(LIRGenerationResult lirGenRes, AllocationContext context) {
        LIR lir = lirGenRes.getLIR();
        AbstractBlockBase<?>[] blocks = lir.getControlFlowGraph().getBlocks();
        Random random = new Random();
        wrongRegisterUseCount = 0;

        for (AbstractBlockBase<?> block : blocks) {
            ArrayList<LIRInstruction> instructions = lir.getLIRforBlock(block);

            for (LIRInstruction instruction : instructions) {

                if (wrongRegisterUseCount < ERROR_COUNT) {
                    instruction.forEachInput(new InstructionValueProcedure() {

                        @Override
                        public Value doValue(LIRInstruction inst, Value value, OperandMode mode, EnumSet<OperandFlag> flags) {

                            if (ValueUtil.isRegister(value)) {
                                RegisterValue register = ValueUtil.asRegisterValue(value);

                                // get all allocatable registers, that have the same register
                                // category as the correct register
                                List<Register> filteredRegisters = getFilteredAllocatableRegistersSamePlatformKind(context, value);

                                if (filteredRegisters.size() == 0) {
                                    return value;
                                }
                                inst.setComment(lirGenRes, "injected wrong register use error");

                                wrongRegisterUseCount++;
                                int index = random.nextInt(filteredRegisters.size());
                                return filteredRegisters.get(index).asValue(register.getValueKind());
                            }

                            return value;
                        }
                    });
                }
            }
        }

        return wrongRegisterUseCount != 0;
    }

    private static List<Register> getFilteredAllocatableRegistersSamePlatformKind(AllocationContext context, Value value) {
        Register[] registers = context.registerAllocationConfig.getAllocatableRegisters(value.getPlatformKind()).allocatableRegisters;

        RegisterValue registerValue = ValueUtil.asRegisterValue(value);
        return Arrays.stream(registers).filter(r -> !r.equals(registerValue.getRegister())).collect(Collectors.toList());
    }
}
