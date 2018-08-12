package org.graalvm.compiler.lir.saraverify;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.graalvm.compiler.debug.DebugContext;
import org.graalvm.compiler.debug.DebugContext.Scope;
import org.graalvm.compiler.debug.Indent;
import org.graalvm.compiler.lir.LIRInstruction;
import org.graalvm.compiler.lir.LIRValueUtil;

import jdk.vm.ci.meta.AllocatableValue;
import jdk.vm.ci.meta.Value;

public class DefAnalysisInfo {

    class Triple {
        private final Value location;
        private final DuSequenceWeb value;
        private final ArrayList<ArrayList<LIRInstruction>> instructionSequences;

        public Triple(Value location, DuSequenceWeb value, LIRInstruction instruction) {
            this.location = SARAVerifyUtil.getValueIllegalValueKind(location);
            this.value = value;
            instructionSequences = new ArrayList<>();

            ArrayList<LIRInstruction> instructionSequence = new ArrayList<>();
            instructionSequence.add(instruction);
            instructionSequences.add(instructionSequence);
        }

        public Triple(Value location, DuSequenceWeb value, ArrayList<ArrayList<LIRInstruction>> instructionSequences) {
            this.location = SARAVerifyUtil.getValueIllegalValueKind(location);
            this.value = value;
            this.instructionSequences = instructionSequences;
        }

        public Value getLocation() {
            return location;
        }

        public DuSequenceWeb getValue() {
            return value;
        }

        public ArrayList<ArrayList<LIRInstruction>> getInstructionSequences() {
            ArrayList<ArrayList<LIRInstruction>> newInstructionSequences = new ArrayList<>();

            for (ArrayList<LIRInstruction> instructionSequence : instructionSequences) {
                newInstructionSequences.add(new ArrayList<>(instructionSequence));
            }

            return newInstructionSequences;
        }

        public boolean containsInstruction(LIRInstruction instruction) {
            for (ArrayList<LIRInstruction> instructionSequence : instructionSequences) {
                if (instructionSequence.contains(instruction)) {
                    return true;
                }
            }

            return false;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            // result = prime * result + instructionSequenceHashCode();
            result = prime * result + location.hashCode();
            result = prime * result + value.hashCode();
            return result;
        }

        private int instructionSequenceHashCode() {
            int hashCode = 1;
            for (ArrayList<LIRInstruction> instructionSequence : instructionSequences) {
                for (LIRInstruction instruction : instructionSequence) {
                    hashCode = 31 * hashCode + (instruction == null ? 0 : System.identityHashCode(instruction));
                }
            }

            return hashCode;
        }

        @Override
        public boolean equals(Object obj) {
            if (!(obj instanceof Triple)) {
                return false;
            }

            Triple triple = (Triple) obj;
            // return equalsLocationAndValue(triple) &&
            // this.instructionSequences.equals(triple.instructionSequences);
            return equalsLocationAndValue(triple);
        }

        /**
         * Indicates whether some other triple is equal to this one regarding the location and the
         * value.
         *
         * @param triple
         * @return true if this triple is the same as the triple argument regarding the location and
         *         the value, otherwise false
         */
        public boolean equalsLocationAndValue(Triple triple) {
            return this.location.equals(triple.location) && this.value.equals(triple.value);
        }

        @Override
        protected Object clone() throws CloneNotSupportedException {
            // TODO: cloning of instruction sequences
            return new Triple(location, value, new ArrayList<>(instructionSequences));
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();

            sb.append("( ");
            sb.append(location);
            sb.append(", ");
            sb.append(String.format("0x%h", value.hashCode()));
            sb.append(", <");

            for (ArrayList<LIRInstruction> instructionSequence : instructionSequences) {
                sb.append(instructionSequence.stream().map(instruction -> instruction.id() + ":" + instruction.name()).collect(Collectors.joining(", ")));
            }

            sb.append("> )");
            return sb.toString();
        }
    }

    /**
     * The location set records that location holds a value. The instruction sequence of a triple
     * denotes the copy operations of the du-sequence.
     */
    private final Set<Triple> locationSet;

    /**
     * The stale set records that location holds a stale value. The instruction sequence of a triple
     * denotes the non-copy instruction that made value in location become stale and the copy
     * instructions that propagate the stale value.
     */
    private final Set<Triple> staleSet;

    /**
     * The eviction set records that the value is evicted from the location. The instruction
     * sequence consists of exactly one instruction, namely the instruction that kills the value
     * from the location.
     */
    private final Set<Triple> evictedSet;

    public DefAnalysisInfo() {
        this.locationSet = new HashSet<>();
        this.staleSet = new HashSet<>();
        this.evictedSet = new HashSet<>();
    }

    public DefAnalysisInfo(Set<Triple> location, Set<Triple> stale, Set<Triple> evicted) {
        this.locationSet = location;
        this.staleSet = stale;
        this.evictedSet = evicted;
    }

    public void logSetSizes(DebugContext debugContext) {
        try (Indent i = debugContext.indent(); Scope s = debugContext.scope(DefAnalysis.DEBUG_SCOPE)) {
            debugContext.log(3, "%s", "Location: " + locationSet.size());
            debugContext.log(3, "%s", "Stale: " + staleSet.size());
            debugContext.log(3, "%s", "Evicted: " + evictedSet.size());
        }
    }

    // TODO: rename or add method equalsLocationAndValue(Triple) to Triple
    public static boolean containsTriple(Triple triple, Set<Triple> set) {
        return set.stream().anyMatch(t -> t.equalsLocationAndValue(triple));
    }

    public static Stream<Triple> locationSetUnionStream(List<DefAnalysisInfo> defAnalysisSets) {
        return defAnalysisSets.stream().flatMap(sets -> sets.locationSet.stream());
    }

    public static Set<Triple> locationSetIntersection(List<DefAnalysisInfo> defAnalysisSets) {
        Stream<Triple> locationUnionStream = locationSetUnionStream(defAnalysisSets);
        Stream<Triple> locationIntersectedStream = locationUnionStream  //
                        .filter(triple -> defAnalysisSets.stream().allMatch(sets -> containsTriple(triple, sets.locationSet)));
        return locationIntersectedStream.collect(Collectors.toSet());
    }

    public static Set<Triple> staleSetUnion(List<DefAnalysisInfo> defAnalysisSets) {
        Stream<Triple> staleUnionStream = defAnalysisSets.stream().flatMap(sets -> sets.staleSet.stream());
        return staleUnionStream.collect(Collectors.toSet());
    }

    public static Set<Triple> evictedSetUnion(List<DefAnalysisInfo> defAnalysisSets) {
        Stream<Triple> evictedUnionStream = defAnalysisSets.stream().flatMap(sets -> sets.evictedSet.stream());
        return evictedUnionStream.collect(Collectors.toSet());
    }

    public List<Triple> getLocationTriples(DuSequenceWeb value) {
        return locationSet.stream().filter(triple -> !LIRValueUtil.isConstantValue(triple.location) && triple.value.equals(value)).collect(Collectors.toList());
    }

    // TODO: remove debug
    public Map<Value, List<Triple>> getGroupedTriples() {
        return locationSet.stream().collect(Collectors.groupingBy(Triple::getLocation));
    }

    public static List<Value> distinctLocations(List<DefAnalysisInfo> defAnalysisInfos) {
        return defAnalysisInfos.stream().flatMap(defAnalysisInfo -> defAnalysisInfo.locationSet.stream())      //
                        .map(triple -> triple.getLocation()).distinct().collect(Collectors.toList());
    }

    /**
     * Returns a list of locations for which there is at least one triple in the location set.
     *
     * @return list of locations from the location set
     */
    public List<Value> getOccupiedLocations() {
        // TODO: remove method?
        return locationSet.stream().map(triple -> triple.getLocation()).distinct().collect(Collectors.toList());
    }

    public List<Triple> getEvictedTriples(DuSequenceWeb value) {
        return evictedSet.stream().filter(triple -> triple.value.equals(value)).collect(Collectors.toList());
    }

    public Triple getStaleTriple(Value location, DuSequenceWeb value) {
        return staleSet.stream().filter(triple -> triple.location.equals(location) && triple.value.equals(value)).findFirst().orElse(null);
    }

    public void addLocation(Value location, DuSequenceWeb value, LIRInstruction instruction, boolean addStaleValues) {
        if (addStaleValues) {
            // find triples in the location set that hold the value in a different location than the
            // location from the argument (except constant values, which can't be stale)
            List<Triple> staleTriples = locationSet.stream()     //
                            .filter(triple -> !LIRValueUtil.isConstantValue(triple.location) && triple.value.equals(value) &&
                                            !triple.location.equals(SARAVerifyUtil.getValueIllegalValueKind(location))) //
                            .collect(Collectors.toList());

            // add triples to the stale set for each stale value
            staleTriples.forEach(triple -> staleSet.add(new Triple(triple.location, triple.value, instruction)));
        }

        // add a triple to the location set for the defined value
        locationSet.add(new Triple(location, value, instruction));
    }

    public void removeFromEvicted(Value locationValue, DuSequenceWeb value) {
        // remove all triples in the evicted set that have the location and the value from the
        // arguments
        evictedSet.removeIf(triple -> triple.location.equals(SARAVerifyUtil.getValueIllegalValueKind(locationValue)) //
                        && triple.value.equals(value));
    }

    public void propagateValue(AllocatableValue result, Value input, LIRInstruction instruction) {
        if (!SARAVerifyUtil.getValueIllegalValueKind(result).equals(SARAVerifyUtil.getValueIllegalValueKind(input))) {
            // destroys the values from the locations of the result
            destroyValuesAtLocations(Arrays.asList(result), instruction);
        }

        // for every triple in the location set that consists of the location "input", a new triple
        // is added to the set, where the location is the argument
        // "result" and the copy instruction is added to the instruction sequence
        List<Triple> triples = locationSet.stream()         //
                        .filter(triple -> triple.location.equals(SARAVerifyUtil.getValueIllegalValueKind(input)) && !triple.containsInstruction(instruction))   //
                        .collect(Collectors.toList());
        triples.forEach(triple -> {
            ArrayList<ArrayList<LIRInstruction>> instructionSequences = new ArrayList<>();

            for (ArrayList<LIRInstruction> instructionSequence : triple.instructionSequences) {
                ArrayList<LIRInstruction> newInstructionSequence = new ArrayList<>(instructionSequence);
                newInstructionSequence.add(instruction);
                instructionSequences.add(newInstructionSequence);
            }

            locationSet.add(new Triple(result, triple.value, instructionSequences));

            removeFromEvicted(result, triple.value);
        });

        // for every triple in the stale set that consists of the location "input", a new triple is
        // added to the set, where the location is the argument
        // "result" and the copy instruction is added to the instruction sequence
        triples = staleSet.stream() //
                        .filter(triple -> triple.location.equals(SARAVerifyUtil.getValueIllegalValueKind(input)) && !triple.containsInstruction(instruction))   //
                        .collect(Collectors.toList());
        triples.forEach(triple -> {
            ArrayList<ArrayList<LIRInstruction>> instructionSequences = new ArrayList<>();

            for (ArrayList<LIRInstruction> instructionSequence : triple.instructionSequences) {
                ArrayList<LIRInstruction> newInstructionSequence = new ArrayList<>(instructionSequence);
                newInstructionSequence.add(instruction);
                instructionSequences.add(newInstructionSequence);
            }

            staleSet.add(new Triple(result, triple.value, instructionSequences));
        });
    }

    public void destroyValuesAtLocations(List<Value> locationValues, LIRInstruction instruction) {
        // makes values with illegal value kind for comparison
        List<Value> locationValuesIllegal = locationValues.stream().map(value -> SARAVerifyUtil.getValueIllegalValueKind(value)).collect(Collectors.toList());

        // triples that have a location where the value gets evicted
        List<Triple> evictedTriples = locationSet.stream().filter(triple -> locationValuesIllegal.contains(triple.location)).collect(Collectors.toList());

        // remove the triples from the locations and the stale set
        locationSet.removeAll(evictedTriples);
        staleSet.removeIf(triple -> locationValuesIllegal.contains(triple.location));

        // add a new triple to the evicted set for each evicted triple
        evictedTriples.stream().forEach(triple -> evictedSet.add(new Triple(triple.location, triple.value, instruction)));
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + evictedSet.hashCode();
        result = prime * result + locationSet.hashCode();
        result = prime * result + staleSet.hashCode();
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof DefAnalysisInfo)) {
            return false;
        }

        DefAnalysisInfo defAnalysisSets = (DefAnalysisInfo) obj;
        return defAnalysisSets.locationSet.equals(locationSet) && defAnalysisSets.staleSet.equals(staleSet) && defAnalysisSets.evictedSet.equals(evictedSet);
    }

    @Override
    protected Object clone() throws CloneNotSupportedException {
        return new DefAnalysisInfo(cloneSet(locationSet), cloneSet(staleSet), cloneSet(evictedSet));
    }

    private static Set<Triple> cloneSet(Set<Triple> set) throws CloneNotSupportedException {
        Set<Triple> clonedSet = new HashSet<>();
        for (Triple triple : set) {
            clonedSet.add((Triple) triple.clone());
        }

        return clonedSet;
    }

}
