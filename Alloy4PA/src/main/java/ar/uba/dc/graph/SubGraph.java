package ar.uba.dc.graph;

import guru.nidi.graphviz.model.MutableGraph;
import guru.nidi.graphviz.parse.Parser;

import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

public class SubGraph {
    String dot_file;
    MutableGraph graph;
    boolean onlyOneCluster;

    public SubGraph(String path_dot_file, boolean onlyOneCluster) {
        this.dot_file = path_dot_file;
        this.graph = loadGraph(dot_file);
        this.onlyOneCluster = onlyOneCluster;
    }

    private MutableGraph loadGraph(String filePath) {
        try {
            return new Parser().read(new File(filePath));
        } catch (IOException e) {
            throw new RuntimeException("No se pudo cargar el archivo Graphviz.", e);
        }
    }

    List<Tuple<String[],List<String>>> getSubgraphs() throws IOException {
        Graph graph = Graph.createFrom(this.dot_file);
        //((action,state),[states_in_group])
        List<Tuple<String[],List<String>>> subgraph_list = new ArrayList<>();
        List<String> subgraph = new ArrayList<>();
        for (Graph.Node goalState : graph.nodes.values()) {
            //Get incoming edges except the loop ones
            Set<Graph.Edge> incomingEdges = goalState.getIncomingEdges().stream().filter(e->!e.getFromNode().equals(e.getToNode())).collect(Collectors.toSet());
            if (incomingEdges.size() < 2)
                continue;
            int differentIncomingActions = incomingEdges.stream().map(Graph.Edge::getName).collect(Collectors.toSet()).size();
            // There is nothing to group
            if (differentIncomingActions == incomingEdges.size())
                continue;
            //For each incoming state, check if it is possible always to reach goalState
            Set<String> actions = incomingEdges.stream().map(Graph.Edge::getName).collect(Collectors.toSet());
            for (String action : actions) {
                String finalAction = action;
                for (Graph.Edge e : incomingEdges.stream().filter(n -> n.getName().equals(finalAction)).collect(Collectors.toSet())) {
//                //If there is just one transition with this name, then continue (because there is nothing to group)
//                if (incoming.stream().noneMatch(p -> p.getName().equals(e.getName()))) {
//                    continue;
//                }

                    //We only want to group blue actions because black actions does not ensure anything
                    if (!e.isBlueAction())
                        continue;

                    String who_action = e.whoDidAction();
                    boolean candidate_whoAction = e.isValidWhoDidAction();

                    boolean candidate = true;
                    //For each outgoing edge from incoming state, check if it is possible always to go state goalState
                    for (Graph.Edge out : e.getFromNode().getOutgoingEdges()) {
                        //Avoid the same edge
                        if (out.equals(e))
                            continue;
                        String who_curr_action = out.whoDidAction();
                        Graph.Node toNode = out.getToNode();
                        //
                        if ((!candidate_whoAction || !who_action.equals(who_curr_action)) && !alwaysPathToS(toNode, goalState, who_action)) {
                            candidate = false;
                        }
                    }
                    if (candidate) {
                        subgraph.add(e.getFromNode().getName());
                        action = e.getName();
                    }
                }
                if (this.onlyOneCluster) {
                    //TODO add these nodes to a set. Avoid looking for these nodes.
                    boolean sameNode = subgraph_list.stream().anyMatch(e->e.second().stream().anyMatch(subgraph::contains));
                    if (sameNode) {
                        System.out.println("Same node in other cluster. Avoiding this clustering: "+subgraph);
                        subgraph.clear();
                    }
                }
                if (subgraph.size() >= 2) {
                    String[] action_state = {action, goalState.getName()};
                    subgraph_list.add(new Tuple<>(action_state, new ArrayList<>(subgraph)));
                }
                subgraph.clear();
            }
        }
        return subgraph_list;
    }
    


    private boolean alwaysPathToS(Graph.Node otherState, Graph.Node targetState, String who_action) {
        return true;
    }

}