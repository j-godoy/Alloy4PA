package ar.uba.dc.partitioner;

import ar.uba.dc.config.Config;
import ar.uba.dc.query.ReduceStatesN;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.stream.Collectors;

import static ar.uba.dc.config.Config.ALLOW_ADDRESS_0x0;
import static ar.uba.dc.config.Config.SUFFIX_GRAPHVIZ_NAME_STATES;
import static ar.uba.dc.config.Config.VERBOSE;

public class AlloyGenerator {

    private Subject subject;

    // Read ini configuration
    public void readConfig(String configPath) throws IOException {
        Path path = Paths.get(configPath);
        Path configDir = path.getParent();
        List<String> lines = Files.readAllLines(path);
        String configBaseName = path.getFileName().toString().replace("Config.ini", "");
        Path pathFile = configDir.getParent().resolve(configBaseName).resolve(configBaseName + ".als");
        String inv = "";
        int states = 0;
        String nombreParticion = "";
        String cantidadObjetosEnRuns = "";
        String epa = "";
        String predicate = "";
        int dividirEstadosPor = 1;

        // Process section - It expects that there is just once
        for (String line : lines) {
            if (line.isEmpty() || line.startsWith(";") || line.startsWith("#")) continue;
            String origLine = line;
            line = line.toLowerCase().replaceAll(" ", "").trim();
            if (line.startsWith("inv=")) {
                try {
                    inv = line.split("=")[1].strip();
                } catch (Exception e) {inv = "";}
            }
            else if (line.startsWith("estados=") || line.trim().startsWith("states=")) {
                try {
                    states = Integer.parseInt(line.split("=")[1].strip());
                } catch (Exception e) {
                    System.err.println("States in config.ini is not set by a number. Setting States=0");
                    states = 0;
                }
            }
            else if (line.startsWith("nombreparticion=") || line.trim().startsWith("partitionname=")) {
                nombreParticion = line.split("=")[1].strip();
            }
            else if (line.startsWith("cantidadobjetosenruns=") || line.trim().startsWith("scope=")) {
                cantidadObjetosEnRuns = origLine.split("=")[1].strip();
            }
            else if (line.toUpperCase().startsWith("EPA=")) {
                epa = line.split("=")[1].strip();
            }
            else if (line.startsWith("predicates=")) {
                try {
                    origLine = origLine.replace("predicates=", "").replace("predicates =", "");
                    origLine = origLine.replace("Predicates=", "").replace("Predicates =", "");
                    predicate = origLine.strip();
                } catch (Exception e) {predicate = "";}

            }
            else if (line.startsWith("dividir_estados_por=") || line.startsWith("divide_states_by=")) {
                String dividirEstadosPorStr = line.split("=")[1].strip();
                if (!dividirEstadosPorStr.trim().isEmpty()) {
                    dividirEstadosPor = Integer.parseInt(dividirEstadosPorStr.trim());
                }
            }
            else if (line.startsWith("query_timeout_limit_in_secs=")) {
                int newTimeout = Integer.parseInt(origLine.split("=")[1].strip());
                if (VERBOSE) {
                    System.out.printf("Updating TO value from '%s' to '%s'\n", Config.QUERY_TIMEOUT_LIMIT_IN_SECS, newTimeout);
                }
                Config.QUERY_TIMEOUT_LIMIT_IN_SECS = newTimeout;
            }
        }

        this.subject = new Subject(inv, states, pathFile.toString(), nombreParticion,
                cantidadObjetosEnRuns, epa, predicate, dividirEstadosPor);
    }

    static String PRED_PREFIX = "pred met_";
    static String MET_PREFIX = "met_";

    private List<String> getSignaturesActions(String filePath) throws IOException {
        List<String> signatures = new ArrayList<>();
        boolean foundPrefix = false;
        StringBuilder currentSig = new StringBuilder();

        for (String line : Files.readAllLines(Paths.get(filePath))) {
            line = line.replace("\n", "").replace("\t", "").trim();
            if (line.contains(PRED_PREFIX)) {
                currentSig = new StringBuilder(line.replace("pred ", ""));
                if (line.contains("]")) {
                    signatures.add(currentSig.toString());
                    currentSig = new StringBuilder();
                    foundPrefix = false;
                } else {
                    foundPrefix = true;
                }
            } else if (foundPrefix) {
                currentSig.append(line);
                if (line.contains("]")) {
                    signatures.add(currentSig.toString());
                    currentSig = new StringBuilder();
                    foundPrefix = false;
                }
            }
        }

        return signatures;
    }

    private Map<String, Integer> getParametersTypesMapFromSignature(String signature) {
        Map<String, Integer> map = new LinkedHashMap<>();
        int start = signature.indexOf("[");
        int end = signature.indexOf("]");
        if (start < 0 || end < 0) return map;

        String[] params = signature.substring(start + 1, end).split(",");
        for (String p : params) {
            String[] parts = p.split(":");
            if (parts.length != 2) continue;
            String type = parts[1].trim();
            if (type.equals("EstadoConcreto")) continue;
            map.put(type, map.getOrDefault(type, 0) + 1);
        }
        return map;
    }

    // Generates a list of predicates for EPA
    private List<List<String>> getEPAPredsList(Subject subject) throws IOException {
        List<String> originalActions = getSignatures(subject.pathFile).stream()
                .map(this::getPreconditionName)
                .filter(a -> !a.equals("constructor"))
                .map(a -> "pre_" + a + "[e]")
                .toList();

        List<List<String>> result = new ArrayList<>();
        int n = originalActions.size();

        result.add(new ArrayList<>(originalActions));

        // For k = 1 to n negations
        for (int k = 1; k <= n; k++) {
            // Generate all combinations of k indices to negate
            List<int[]> combos = combinations(n, k);
            for (int[] combo : combos) {
                List<String> comboList = new ArrayList<>();
                for (int i = 0; i < n; i++) {
                    boolean negate = false;
                    for (int c : combo) {
                        if (c == i) {
                            negate = true;
                            break;
                        }
                    }
                    if (negate) {
                        comboList.add("not " + originalActions.get(i));
                    } else {
                        comboList.add(originalActions.get(i));
                    }
                }
                result.add(comboList);
            }
        }
        return result;
    }

    // Generate all combinations (subsets) of size k from the set {0, ..., n-1}
    private List<int[]> combinations(int n, int k) {
        List<int[]> result = new ArrayList<>();
        combineHelper(result, new int[k], 0, n - 1, 0);
        return result;
    }

    // Recursive helper to generate combinations
    private void combineHelper(List<int[]> result, int[] temp, int start, int end, int index) {
        if (index == temp.length) {
            result.add(temp.clone());
            return;
        }
        for (int i = start; i <= end && end - i + 1 >= temp.length - index; i++) {
            temp[index] = i;
            combineHelper(result, temp, i + 1, end, index + 1);
        }
    }


    private List<String> getSignatures(String pathFile) throws IOException {
        List<String> signatures = new ArrayList<>();
        List<String> lines = Files.readAllLines(Paths.get(pathFile));
        boolean foundPrefijo = false;
        String sig = "";
        for (String line : lines) {
            if (line.contains("pred met_")) {
                sig = line.replace("pred ", "").trim();
                if (sig.contains("]")) {
                    int endIdx = sig.indexOf("]") + 1;
                    sig = sig.substring(0, endIdx);
                    signatures.add(sig);
                    foundPrefijo = false;
                } else {
                    foundPrefijo = true;
                }
            } else if (foundPrefijo) {
                if (line.contains("]")) {
                    int endIdx = line.indexOf("]") + 1;
                    sig += line.substring(0, endIdx);
                    signatures.add(sig);
                    foundPrefijo = false;
                } else {
                    sig += line.trim();
                }
            }
        }
        return signatures;
    }


    // Format the name of a state, SXX, with leading zeros
    private static String stateName(int num) {
        return (num < 10) ? "S0" + num : "S" + num;
    }

    // Gets the name of the precondition of a Signature
    private String getPreconditionName(String signature) {
        if (signature == null || signature.isEmpty()) return "";
        return signature.split("\\[")[0].replace(MET_PREFIX, "");
    }

    private String createEPPartition(Subject subject) throws IOException {
        List<List<String>> predsList = getEPAPredsList(subject);
        StringBuilder partitions = new StringBuilder();
        Path path = Paths.get(subject.pathFile);
        boolean tieneS00 = Files.readAllLines(path).stream().anyMatch(line -> line.contains("S00"));

        if (!tieneS00) {
            partitions.append(String.format("pred %sS00[e: EstadoConcreto]{\n", subject.nombreParticion));
            partitions.append("\t(e._init = False)\n");
            partitions.append("}\n\n");
        }

        if (!subject.inv.isEmpty()) {
            partitions.append(String.format("pred %s%s[e: EstadoConcreto]{\n", subject.nombreParticion, subject.inv));
            partitions.append("\tnot invariante[e]\n");
            partitions.append("}\n\n");
        }

        List<String> predicates = getPredicates(subject);
        int numPreds = predicates.size();
        int numEPAStates = predsList.size();
        StringBuilder graphvizContent = new StringBuilder();

        for (int p = 0; p < numPreds; p++) {
            for (int n = 0; n < numEPAStates; n++) {
                String stateName = stateName((n + 1) + p * numEPAStates);
                partitions.append(String.format("pred partition%s[e: EstadoConcreto]{\n", stateName));
                partitions.append("\t(invariante[e])\n");

                List<String> currentList = predsList.get(n);
                StringBuilder line = new StringBuilder();
                StringBuilder forGraphviz = new StringBuilder(stateName + " [label=\"");

                for (int i = 0; i < currentList.size(); i++) {
                    String curr = currentList.get(i).trim();
                    if (curr.isEmpty()) continue;

                    String nameForGraphviz = curr.replace("not ", "").replace("[e]", "").replace("pre_", "");
                    if (curr.startsWith("not ")) nameForGraphviz = "!" + nameForGraphviz;

                    if (i > 0) {
                        line.append(" and ");
                        forGraphviz.append(" & ");
                    }
                    line.append(curr);
                    forGraphviz.append(nameForGraphviz);

                    if ((i + 1) % 2 == 0) forGraphviz.append("\\n");
                }

                if (!line.toString().isEmpty()) partitions.append("\t").append(line).append("\n");

                String pred = predicates.get(p).trim();
                if (!pred.isEmpty()) {
                    partitions.append("\t").append(pred).append("\n");
                    forGraphviz.append(" & ").append(pred.replace(" and ", " & "));
                }

                partitions.append("}\n\n");
                forGraphviz.append("\"]\n");
                graphvizContent.append(forGraphviz);
            }
        }

        // Write the file _graphviz_names_states.txt with meaningful names for states
        Path outputGraphviz = Paths.get(subject.pathFile.replace(".als", SUFFIX_GRAPHVIZ_NAME_STATES));
        Files.writeString(outputGraphviz, graphvizContent.toString());

        return partitions.toString();
    }



    // It parses the predicates from the subject and returns a list of predicates.
    // If the subject has no predicates, it returns a list with an empty string.
    private List<String> getPredicates(Subject subject) {
        if (subject == null || subject.predicate == null) return Collections.singletonList("");
        String trimmed = subject.predicate.trim();
        if (trimmed.isEmpty()) return Collections.singletonList("");
        return Arrays.stream(trimmed.split(",")).map(String::trim).collect(Collectors.toList());
    }

    private List<Integer> getReachableStates(Subject subject, int statesNumber) throws IOException {
        String outputStatesValidPath = subject.pathFile.replace(".als", "_valid_states");
        String alloy_file = subject.pathFile;
        String states = String.valueOf(statesNumber);
        String scope = subject.cantidadObjetosEnRuns;

        ReduceStatesN reduceStates = new ReduceStatesN(alloy_file, outputStatesValidPath, states, scope);
        return reduceStates.getValidStateNumbers();
    }

    private String createTransitions(Subject subject, List<Integer> sliceValidStates, List<Integer> reachableStates) throws IOException {
        StringBuilder transitionsAndRuns = new StringBuilder();
        List<String> signatures = getSignaturesActions(subject.pathFile);

        for (String sig : signatures) {
            String action = getActionNameFromSignature(sig);
            StringBuilder preds = new StringBuilder();
            StringBuilder transitions = new StringBuilder();

            for (int ori : sliceValidStates) {
                String partitionName = subject.nombreParticion;

                // Only constructor in S00, and no other action in S00
                if (ori != 0 && action.contains("met_constructor")) continue;
                if (ori == 0 && !action.contains("met_constructor")) continue;

                for (int dst : reachableStates) {
                    // Only check reachability of valid states
                    if (dst == 0) continue;

                    preds.append(newTransitionPred(partitionName, stateName(ori), stateName(dst), sig));
                    transitions.append(String.format("run transition__%s__a__%s__mediante_%s for %s\n",
                            stateName(ori), stateName(dst), action, subject.cantidadObjetosEnRuns));
                }

                // Transition to the state that breaks the invariant
                if (!subject.inv.isEmpty()) {
                    preds.append(newTransitionPred(partitionName, stateName(ori), subject.inv, sig));
                    transitions.append(String.format("run transition__%s__a__%s__mediante_%s for %s\n",
                            stateName(ori), subject.inv, action, subject.cantidadObjetosEnRuns));
                }
            }

            transitionsAndRuns.append(preds).append(transitions);
        }

        return transitionsAndRuns.toString();
    }

    private String newTransitionPred(String partitionName, String ori, String dst, String signature) {
        String action = getActionNameFromSignature(signature);
        Map<String, Integer> types = getParametersTypesMapFromSignature(signature);

        List<String> decTypes = new ArrayList<>();
        List<String> vars = new ArrayList<>();
        String sender = "";
        int varType = 1;

        for (Map.Entry<String, Integer> entry : types.entrySet()) {
            String type = entry.getKey();
            int count = entry.getValue();
            for (int i = 0; i < count; i++) {
                String varName = "v" + varType + i;
                vars.add(varName);
                decTypes.add(varName + ":" + type);
                // To prevent sender = Address0x0. This only works if sender
                // is the first parameter of type Address in the Alloy predicate
                if (ALLOW_ADDRESS_0x0 && sender.isEmpty() && type.equals("Address")) {
                    sender = varName;
                }
            }
            varType++;
        }

        StringBuilder pred = new StringBuilder();
        pred.append(String.format("pred transition__%s__a__%s__mediante_%s{\n", ori, dst, action));

        String allParams = String.join(", ", decTypes);
        if (!allParams.isEmpty()) {
            allParams = ", " + allParams;
        }

        String condSender = (!sender.isEmpty()) ? sender + " != Address0x0 and " : "";
        String argsCall = vars.isEmpty() ? "" : ", " + String.join(", ", vars);

        pred.append(String.format("\t(some x,y:EstadoConcreto%s |\n", allParams));
        pred.append(String.format("\t\t%s%s[x] and %s%s[y] and\n", partitionName, ori, partitionName, dst));
        pred.append(String.format("\t\t%s%s[x, y%s])\n", condSender, action, argsCall));
        pred.append("}\n\n");

        return pred.toString();
    }

    private String getActionNameFromSignature(String signature) {
        return signature.split("\\[")[0];
    }

    public void run() throws Exception {
        readConfig(this.configFilePath);

        if (subject == null) {
            throw new RuntimeException("No section was found in the configuration file\n.");
        }

        int numberStates;
        int maxState;

        int DIVIDO_POR = this.subject.dividirEstadosPor;
        long startTime = System.currentTimeMillis();

        String partitionsPredicates;
        List<Integer> reachableStates = new ArrayList<>();
        if ("true".equalsIgnoreCase(this.subject.epa)) {
            this.subject.states = getEPAPredsList(this.subject).size();
            partitionsPredicates = createEPPartition(this.subject);

            Files.writeString(Paths.get(this.subject.pathFile), "\n\n" + partitionsPredicates, StandardOpenOption.APPEND);

            numberStates = this.subject.states * getPredicates(this.subject).size();
            reachableStates = getReachableStates(this.subject, numberStates);

            maxState = reachableStates.size() / DIVIDO_POR;
        } else {
            numberStates = this.subject.states;
            for (int i = 0; i <= this.subject.states; i++) {
                reachableStates.add(i);
            }
            maxState = numberStates / DIVIDO_POR;
        }

        int INC = maxState;
        int desde = 0;
        int hasta = maxState;
        int cont = 1;
        String sufijo;

        while (hasta <= reachableStates.size()) {
            List<Integer> slice = reachableStates.subList(desde, hasta);
            String queries = createTransitions(this.subject, slice, reachableStates);

            String[] fileSplit = this.subject.pathFile.split("\\."); // divide en nombre y extensión
            String newFile = this.subject.pathFile;

            if (hasta < reachableStates.size() || cont > 1) {
                sufijo = "_part" + cont;
                newFile = fileSplit[0] + sufijo + "." + fileSplit[1];

                // Copy original file to new file
                Files.copy(Paths.get(this.subject.pathFile), Paths.get(newFile), StandardCopyOption.REPLACE_EXISTING);
                cont++;
            }

            Files.writeString(Paths.get(newFile), "\n\n\n" + queries, StandardOpenOption.APPEND);

            desde = hasta;
            if (hasta < reachableStates.size()) {
                if (hasta + INC > reachableStates.size()) {
                    hasta = reachableStates.size();
                } else {
                    hasta += INC;
                }
            } else {
                break;
            }
        }

        long endTime = System.currentTimeMillis();
        if (VERBOSE) {
            System.out.printf("Total time generating alloy file with partitions and preds: %.2f min%n", (endTime - startTime) / 60000.0);
        }
    }

    String configFilePath;
    public AlloyGenerator(String configFile) {
        this.configFilePath = configFile;
    }
}


