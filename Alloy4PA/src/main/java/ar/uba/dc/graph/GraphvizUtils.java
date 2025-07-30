package ar.uba.dc.graph;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class GraphvizUtils {

    public static List<Transition> queriesNotAvailable = new ArrayList<>();

    public static void resetQueriesNotAvailable() {
        queriesNotAvailable = new ArrayList<>();
    }

    private String dotTransitionsSubgraph(SubGraph subGraph, Collection<Transition> transitions) throws IOException {
        StringBuilder clusters = new StringBuilder();
        StringBuilder allTransitions = new StringBuilder();
        int cluster_n = 0;
        for (Tuple<String[], List<String>> s : subGraph.getSubgraphs()) {
            clusters.append("subgraph cluster").append(cluster_n).append(" {\n");
            for (String state : s.second()) {
                clusters.append(state).append("\n");
            }
            clusters.append("}\n");
            String someStateInSubGraph = s.second().get(0);
            String action = s.first()[0];
            String goalState = s.first()[1];
            allTransitions.append(String.format("%s->%s [label=\"%s\", color=\"blue\", ltail=cluster%d];\n", someStateInSubGraph,
                    goalState, action, cluster_n));
            cluster_n++;
        }

        //Do not add transitions who source state is already in some subgraph
        Set<Transition> transitions_filtered = new HashSet<>();
        for (Transition t : transitions) {
            boolean addT = true;
            for (Tuple<String[], List<String>> s : subGraph.getSubgraphs()) {
                for (String stateInGroup : s.second()) {
                    String action = s.first()[0];
                    String goalState = s.first()[1];
                    if (t.initialState().equals(stateInGroup) && t.finalState().stream().anyMatch(e -> e.first().equals(goalState)) && action.equals(t.action())) {
                        addT = false;
                    }
                }
            }
            if (addT) {
                transitions_filtered.add(t);
            }
        }
        allTransitions.append(dotTransitions(transitions_filtered, true));

        return clusters + allTransitions.toString();
    }

    private String reachableStates(String filePathStatesNames, Collection<Transition> transitions) throws IOException {
        Path path = Paths.get(filePathStatesNames);
        if (!Files.exists(path))
            return "";
        List<String> state_names_lines = Files.readAllLines(path);
        StringBuilder filteredStates = new StringBuilder();
        filteredStates.append("S00 [label=\"Init\"]").append("\n");
        for (String l : state_names_lines) {
            String name = l.split(" ")[0];
            if (transitions.stream().anyMatch(t -> t.finalState().stream().anyMatch(e -> e.first().equals(name)) || t.initialState().equals(name))) {
                filteredStates.append(l).append("\n");
            }
        }
        return filteredStates.toString();
    }

    private String dotTransitions(Collection<Transition> transitions, boolean parsed) {
        StringBuilder stringBuilder = new StringBuilder();
        for (Transition transition : transitions) {
            String t = parsed ? transition.dot_transition_parsed() : transition.dot_transition_original();
            stringBuilder.append(t).append("\n");
        }
        return stringBuilder.toString();
    }

    private void writeDotFile(String filePath, boolean compound, String states, String transitions) throws IOException {
        FileWriter file = new FileWriter(filePath);
        PrintWriter pw = new PrintWriter(file);
        pw.println("digraph {");
        if (compound) {
            pw.println("compound=true;");
        }
        pw.print(states);
        pw.println("");
        pw.print(transitions);
        pw.print("}");
        pw.close();
        file.close();
    }

    /**
     * Write the dot file without state names
     */
    public void writeDotFile(String filePath, Collection<Transition> transitions) throws IOException {
        writeDotFile(filePath, false, "", dotTransitions(transitions, false));
    }

    public void writeDotFileReachable(String filePath, Collection<Transition> transitions) throws IOException {

        writeDotFile(filePath, false, "", dotTransitions(transitions, false));
    }



    /**
     * Write the dot file WITH state names and compacting transitions
     */
    public void writeDotFile(String filePath, String filePathStateNames, Collection<Transition> transitions)
            throws IOException {
        String states = reachableStates(filePathStateNames, transitions);
        writeDotFile(filePath, false, states, dotTransitions(transitions, true));
    }

    /**
     * Write the dot file WITH state names and compacting transitions and with sub-graphs if any exists
     */
    public void writeDotFile(String filePath, String filePathStateNames, Collection<Transition> transitions,
                             SubGraph subGraph) throws IOException {
        String states = reachableStates(filePathStateNames, transitions);
        writeDotFile(filePath, true, states, dotTransitionsSubgraph(subGraph, transitions));
    }

    public void writeDotFileForkedArrows(String forkedAndParsedDot, String newPath) {
        try {
            Path path = Paths.get(forkedAndParsedDot);
            Map<String, Map<String, List<String>>> graph = parseGraph(path);
            updateToPataDeGallo(graph);
            String dot = getDotText(graph);

            Path newFile = Paths.get(newPath);
            Files.write(newFile, dot.getBytes(StandardCharsets.UTF_8));
            System.out.println("Saving file " + newFile + "...");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static Map<String, Map<String, List<String>>> parseGraph(Path file) throws IOException {
        Map<String, Map<String, List<String>>> graphDict = new HashMap<>();
        List<String> lines = Files.readAllLines(file, StandardCharsets.UTF_8);

        for (String line : lines) {
            line = line.trim();
            if (line.contains("->")) {
                // Example line: S02->S03 [label="complete", style="", color="blue"]
                String[] parts = line.split("->");
                String source = parts[0].trim();
                String target = parts[1].split(" ")[0].trim();

                String label = extractValue(parts[1], "label=").replace("\"", "");
                String color = extractValue(parts[1], "color=").replace("\"", "").replace("]", "");
                label = label.equals("t") ? "τ" : label;

                if (!List.of("black", "red", "blue").contains(color)) {
                    for (String lab : label.split("\\\\n")) {
                        lab = lab.equals("t") ? "τ" : lab;
                        String key = lab + "_" + color;
                        graphDict.computeIfAbsent(source, k -> new HashMap<>())
                                .computeIfAbsent(key, k -> new ArrayList<>())
                                .add(target);
                    }
                } else {
                    String key = label + "_" + color;
                    graphDict.computeIfAbsent(source, k -> new HashMap<>())
                            .computeIfAbsent(key, k -> new ArrayList<>())
                            .add(target);
                }
            } else if (!line.startsWith("digraph") && !line.contains("}")) {
                graphDict.computeIfAbsent("-", k -> new HashMap<>())
                        .computeIfAbsent("-", k -> new ArrayList<>())
                        .add(line);
            }
        }

        return graphDict;
    }

    private static String extractValue(String input, String key) {
        Pattern pattern = Pattern.compile(key + "\\\"([^\\\"]*)");
        Matcher matcher = pattern.matcher(input);
        return matcher.find() ? matcher.group(1) : "";
    }

    public static void updateToPataDeGallo(Map<String, Map<String, List<String>>> graphDict) {
        Map<String, Map<String, List<String>>> copy = new HashMap<>(graphDict);

        for (String source : copy.keySet()) {
            if (source.equals("-")) continue;

            for (String key : copy.get(source).keySet()) {
                String[] parts = key.split("_");
                String label = parts[0];
                String color = parts[1];
                if (!List.of("black", "red", "blue").contains(color)) {
                    graphDict.computeIfAbsent("-", k -> new HashMap<>())
                            .computeIfAbsent("-", k -> new ArrayList<>())
                            .add(source + "_" + label + " [label=\"\", shape=\"point\", color=\"blue\"]");
                }
            }
        }
    }

    private String getDotText(Map<String, Map<String, List<String>>> graphDict) {
        StringBuilder dot = new StringBuilder("digraph {\n\n");

        for (String state : graphDict.getOrDefault("-", Collections.emptyMap()).getOrDefault("-", List.of())) {
            dot.append(state).append("\n");
        }
        dot.append("\n");

        for (String source : graphDict.keySet()) {
            if (source.equals("-")) continue;
            for (Map.Entry<String, List<String>> entry : graphDict.get(source).entrySet()) {
                String[] parts = entry.getKey().split("_");
                String label = parts[0];
                String color = parts[1];
                String style = color.equals("blue") ? "dotted" : "";
                boolean addLabel = true;

                for (String target : entry.getValue()) {
                    if (!List.of("black", "red", "blue").contains(color)) {
                        if (addLabel) {
                            dot.append(source).append("->").append(source).append("_").append(label)
                                    .append(" [label=\"").append(label).append("\", style=\"dotted")
                                    .append("\", color=\"").append("blue").append("\"]\n");
                            addLabel = false;
                        }
                        dot.append(source).append("_").append(label).append("->").append(target)
                                .append(" [label=\"\", style=\"dotted")
                                .append("\", color=\"").append("blue").append("\"]\n");
                    } else
                    {
                        dot.append(source).append("->").append(target)
                                .append(" [label=\"").append(label).append("\", style=\"").append(style)
                                .append("\", color=\"").append(color).append("\"]\n");
                    }
                }
            }
        }

        dot.append("}");
        return dot.toString();
    }
}
