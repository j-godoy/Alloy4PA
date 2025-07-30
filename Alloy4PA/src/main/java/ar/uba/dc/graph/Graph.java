package ar.uba.dc.graph;

import ar.uba.dc.EPA.AEPA;
import guru.nidi.graphviz.model.*;
import guru.nidi.graphviz.parse.Parser;

import java.io.File;
import java.io.IOException;

import java.util.*;

public class Graph {
    Map<String, Node> nodes = new HashMap<>();
    private final Map<String, Edge> edges = new HashMap<>();

    public static Graph createFrom(String path) throws IOException {
        MutableGraph mutableGraph = new Parser().read(new File(path));
        Graph graph = new Graph();
        mutableGraph.edges().forEach(edge -> {
            String fromNodeName = String.valueOf(edge.from().name());
            String toNodeName = String.valueOf(edge.to().name());
            String edgeName = edge.attrs().get("label").toString();
            String edgeColor = edge.attrs().get("color") != null ? edge.attrs().get("color").toString() : "black";

            graph.addNode(fromNodeName);
            graph.addNode(toNodeName);
            graph.addEdge(edgeName, fromNodeName, toNodeName, edgeColor);
        });
        return graph;
    }

    public void addEdgeFromPredicate(String edgeName, String fromNodeName, String toNodeName, String edgeColor) {
        this.addNode(fromNodeName);
        this.addNode(toNodeName);
        this.addEdge(edgeName, fromNodeName, toNodeName, edgeColor);
    }

    public void addNode(String nodeName) {
        if (!nodes.containsKey(nodeName))
            nodes.put(nodeName, new Node(nodeName));
    }

    public void addEdge(String edgeName, String fromNodeName, String toNodeName, String edgeColor) {
        Node fromNode = getNode(fromNodeName);
        Node toNode = getNode(toNodeName);
        Edge edge = new Edge(edgeName, fromNode, toNode, edgeColor);
        fromNode.addEdge(edge);
        toNode.addIncomingEdge(edge);
        edges.put(edge.toString(), edge);
    }

    public Node getNode(String nodeName) {
        return nodes.get(nodeName);
    }

    public Edge getEdge(String edgeName) {
        return edges.get(edgeName);
    }

    public Set<Node> getIncomingNodes(Node targetNode) {
        Set<Node> incomingNodes = new HashSet<>();
        for (Edge edge : edges.values()) {
            if (edge.getToNode() == targetNode) {
                incomingNodes.add(edge.getFromNode());
            }
        }
        return incomingNodes;
    }

    public Set<Node> getOutgoingNodes(Node sourceNode) {
        return sourceNode.getOutgoingNodes();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Graph otherGraph = (Graph) o;

        if (!Objects.equals(nodes.keySet(), otherGraph.nodes.keySet())) {
            return false;
        }

        // Compara aristas
        for (Edge edge : edges.values()) {
            Edge otherEdge = otherGraph.edges.get(edge.getName());
            if (otherEdge == null) {
                return false; // Falta una arista en el otro grafo
            }

            if (!edge.getName().equals(otherEdge.getName()) ||
                    !edge.getColor().equals(otherEdge.getColor()) ||
                    !edge.getToNode().equals(otherEdge.getToNode())) {
                return false;
            }
        }

        return true;
    }

    public static class Node {
        private final String name;
        private final Set<Edge> outgoingEdges = new HashSet<>();
        private final Set<Edge> incomingEdges = new HashSet<>();

        public Node(String name) {
            this.name = name;
        }

        public String getName() {
            return name;
        }

        public void addEdge(Edge edge) {
            outgoingEdges.add(edge);
        }

        public void addIncomingEdge(Edge edge) {
            incomingEdges.add(edge);
        }

        public Set<Edge> getOutgoingEdges() {
            return outgoingEdges;
        }

        public Set<Edge> getIncomingEdges() {
            return incomingEdges;
        }

        @Override
        public String toString() {
            return name;
        }

        public Set<Node> getOutgoingNodes() {
            Set<Node> outgoingNodes = new HashSet<>();
            for (Edge edge : outgoingEdges) {
                outgoingNodes.add(edge.getToNode());
            }
            return outgoingNodes;
        }
    }

    public static class Edge {
        private final String name;
        private final Node fromNode;
        private final Node toNode;
        private final String color;

        public Edge(String name, Node fromNode, Node toNode, String color) {
            this.name = name;
            this.fromNode = fromNode;
            this.toNode = toNode;
            this.color = color;
        }

        public String getName() {
            return name;
        }

        //method should end with _byA for example
        public String whoDidAction() {
            if (!this.name.contains("_"))
                return "";
            return this.name.substring(name.lastIndexOf("_") + 1);
        }

        public boolean isValidWhoDidAction() {
            return !this.whoDidAction().isBlank();
        }

        public Node getFromNode() {
            return fromNode;
        }

        public Node getToNode() {
            return toNode;
        }

        public String getColor() {
            return color;
        }

        public boolean isBlueAction() {
            return this.color.equals(AEPA.TYPE.BLUE.getColor());
        }
    }
}
