package ar.uba.dc.graph;

import guru.nidi.graphviz.model.Link;
import guru.nidi.graphviz.model.MutableGraph;
import guru.nidi.graphviz.model.MutableNode;
import guru.nidi.graphviz.parse.Parser;

import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

public class Transition {
    private final String initialState;
    private final List<Tuple<String, String>> finalState;//<state,color>
    private final String action;
    private final String string;

    public Transition(String transitionName) {
        int index_first_underscore = transitionName.indexOf("_transition");
        String color = index_first_underscore != -1 ? transitionName.substring(0,index_first_underscore) : "black";
        int init_initstate = transitionName.indexOf("__") + 2;
        int end_initstate = transitionName.indexOf("__a__");
        this.initialState = transitionName.substring(init_initstate, end_initstate);
        int init_tostate = end_initstate + 5;
        int end_tostate = transitionName.indexOf("__", init_tostate);
        String toState = transitionName.substring(init_tostate, end_tostate);
        this.finalState = new ArrayList<>();
        if (!toState.contains("_")) { //has many states
            finalState.add(new Tuple<>(toState, color));
        } else {
            Arrays.stream(toState.split("_")).forEach(e->finalState.add(new Tuple<>(e, color)));
        }
        this.action = transitionName.substring(transitionName.indexOf("_met_") + 5);
        this.string = transitionName;
    }

    public Transition(String from, String to, String action, String color) {
        this.initialState = from;
        this.finalState = new ArrayList<>(List.of(new Tuple<>(to, color)));
        this.action = action.replaceAll("τ", "t").replaceAll("\"", "");
        this.string = "";
    }

    public Transition(String from, List<Tuple<String, String>> to, String action) {
        this.initialState = from;
        this.finalState = to;
        this.action = action.replaceAll("τ", "t").replaceAll("\"", "");
        this.string = "";
    }

    public String action() {
        return this.action;
    }

    public String initialState() {
        return initialState;
    }

    public List<Tuple<String, String>> finalState() {
        return finalState;
    }

    @Override
    public String toString() {
        return String.format("%s->%s by %s", initialState, finalState.stream().map(Tuple::first).collect(Collectors.toList()), action);
    }

    private String dot_transition(boolean parse) {
        String action = this.action.replace("met_", "");
        String style = "";
        if (parse && action.equals("t")) {
            action = "τ";
            style = "dashed";
        }
        StringJoiner sj = new StringJoiner("\n");
        for (Tuple<String, String> t : finalState) {
            String toState = t.first();
            String color = t.second();
            boolean queryNotAvailable = GraphvizUtils.queriesNotAvailable.stream().anyMatch(e -> {
                boolean sameInitialState =  e.initialState().equals(this.initialState());
                boolean sameAction = e.action().equals(this.action());
                boolean sameEndStateAndColor = e.finalState().stream().anyMatch(f->f.first().equals(t.first()) && t.second().equals("black"));
                return sameInitialState && sameAction && sameEndStateAndColor;
            });
            if (queryNotAvailable) {
                color = "red";
            }
            sj.add(String.format("%s->%s [label=\"%s\", style=\"%s\", color=\"%s\"]", this.initialState, toState, action, style, color));
        }
        return sj.toString();
    }

    public String dot_transition_parsed() {
        return this.dot_transition(true);
    }

    public String dot_transition_original() {
        return this.dot_transition(false);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Transition that)) return false;
        return Objects.equals(initialState, that.initialState) && Objects.equals(finalState, that.finalState) && Objects.equals(action, that.action) && Objects.equals(string, that.string);
    }

    @Override
    public int hashCode() {
        return Objects.hash(initialState, finalState, action, string);
    }

    public static Set<Transition> readTransitionsFromDotFile(String dotFilePath) {
        Set<Transition> ret = new HashSet<>();
        try {
            File dotPath = new File(dotFilePath);
            Parser parser = new Parser();
            MutableGraph graph = parser.read(dotPath);
            Map<String, List<Tuple<String,String>>> transitionsMap = new HashMap<>();
            for (MutableNode node : graph.nodes()) {
                for (Link link : node.links()) {
                    assert link.from() != null;
                    String from = link.from().name().toString();
                    String to = link.to().name().toString();
                    String action = Objects.requireNonNull(link.attrs().get("label")).toString();
                    String color = link.attrs().get("color") != null ? Objects.requireNonNull(link.attrs().get("color")).toString() : "black";
                    String key = from+"-"+action;
                    Tuple<String, String> to_color = new Tuple<>(to, color);
                    if (transitionsMap.containsKey(key)){
                        transitionsMap.get(key).add(to_color);
                    } else {
                        transitionsMap.put(key, new ArrayList<>(List.of(to_color)));
                    }
                }
            }
            for (String key : transitionsMap.keySet()) {
                String from = key.split("-")[0];
                String action = key.split("-")[1];
                Transition t = new Transition(from, transitionsMap.get(key), action);
                ret.add(t);
            }
        } catch (IOException e) {
            System.err.println("Error al leer el archivo .dot: " + e.getMessage());
        }
        return ret;
    }

    public static List<Transition> getReachableTransitions(String initialStateName, Collection<Transition> transitions) {
        List<Transition> ret = new ArrayList<>();
        for (Transition t : transitions) {
            if (t.initialState.equals(initialStateName))
                ret.add(t);
        }
        addReachable(ret, transitions);
        return ret;
    }

    public List<List<String>> toStatesCombination() {
        return this.generateCombinations(finalState.stream().map(Tuple::first).collect(Collectors.toList()));
    }

    private static void addReachable(List<Transition> reachables, Collection<Transition> all) {
        int len_before = reachables.size();
        for (Transition t : all) {
            if (!reachables.contains(t) && reachables.stream().anyMatch(s -> s.finalState.stream().anyMatch(e2->e2.first().equals(t.initialState))))
                reachables.add(t);
        }
        if (reachables.size() == len_before)
            return;
        addReachable(reachables, all);
    }

    public static List<Transition> compactActions(Collection<Transition> transitions) {
        Map<String, List<String>> transitionsMap = new HashMap<>();
        String sep = "#";
        // sort transition to get always the same order in parsed
        List<Transition> sortedTransitions = new ArrayList<>(transitions.stream().toList());
        sortedTransitions.sort(Comparator.comparing((Transition o) -> o.initialState).thenComparing(Transition::action));
        for (Transition t : sortedTransitions) {
            for (Tuple<String, String> tuple : t.finalState()) {
                String key = t.initialState() + sep + tuple.first() + sep + tuple.second();
                if (transitionsMap.containsKey(key)) {
                    List<String> curr = transitionsMap.get(key);
                    if (!curr.contains(t.action)) {
                        curr.add(t.action);
                        transitionsMap.put(key, curr);
                    }
                } else {
                    List<String> newAction = new ArrayList<>();
                    newAction.add(t.action);
                    transitionsMap.put(key, newAction);
                }
            }
        }
        List<Transition> ret = new ArrayList<>();
        for (String key : transitionsMap.keySet()) {
            String from = key.split(sep)[0];
            String to = key.split(sep)[1];
            String color = key.split(sep)[2];
            StringJoiner sj = new StringJoiner("\\n");
            transitionsMap.get(key).forEach(sj::add);
            Transition t = new Transition(from, to, sj.toString(), color);
            ret.add(t);
        }
        return ret;
    }

    private List<List<String>> generateCombinations(List<String> elementos) {
        List<List<String>> combinations = new ArrayList<>();
        for (int r = 2; r <= elementos.size(); r++) {
            generateCombinationsAux(elementos, 0, r, new ArrayList<>(), combinations);
        }
        return combinations;
    }

    private void generateCombinationsAux(List<String> elementos, int index, int r, List<String> currCombination, List<List<String>> combinations) {
        if (r == 0) {
            combinations.add(new ArrayList<>(currCombination));
            return;
        }
        if (index == elementos.size()) {
            return;
        }

        currCombination.add(elementos.get(index));
        generateCombinationsAux(elementos, index + 1, r - 1, currCombination, combinations);
        currCombination.remove(currCombination.size() - 1);

        generateCombinationsAux(elementos, index + 1, r, currCombination, combinations);
    }

//    @Override
//    public int compareTo(Object o) {
//        Transition other = (Transition) o;
//        List
//    }
}