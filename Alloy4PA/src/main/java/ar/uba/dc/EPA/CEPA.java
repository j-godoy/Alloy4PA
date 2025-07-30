package ar.uba.dc.EPA;

import ar.uba.dc.graph.GraphvizUtils;
import ar.uba.dc.graph.Transition;
import ar.uba.dc.graph.Tuple;

import java.io.File;
import java.io.IOException;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.ExecutionException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public abstract class CEPA extends AEPA {

    //[method_name]:[concrete parameters in alloy separated by comma] ; [method_name]:[concrete parameters in alloy separated by comma];...
    //Ex: constructor: sender = AddressA, auctionStart > 3, auctionStart < 5;
    public static String STRATEGY = "";
    public static String SENDER_STRATEGY = "";
    public static String SCOPE = "";
    public static Map<String, Tuple<String, List<String>>> STRATEGIES = new HashMap<>();
    public static boolean STRATEGIES_ON;

    protected String dot_epa_reachable;
    public String path_merge_dot;
    public String suffix_output_original_color;
    public String suffix_merged_epa_cepa;

    public static void resetParameters() {
        STRATEGY = "";
        SENDER_STRATEGY = "";
        SCOPE = "";
        STRATEGIES_ON = false;
    }

    CEPA(TYPE type, String alloy_file_path, boolean satisfiable, String suffix_output, List<String> runOnlyPredsStartingWithThisName) {
        super(type, alloy_file_path, satisfiable, suffix_output, runOnlyPredsStartingWithThisName);

        // loadStrategy();

        if (STRATEGIES_ON && !BEPA.STRATEGY.isBlank() && STRATEGIES.isEmpty()) {
            for (String e : BEPA.STRATEGY.split(";")) {
                String method = e.split(":")[0].strip();
                String strategy = e.split(":")[1].strip();
                if (STRATEGIES.containsKey(method)) {
                    throw new RuntimeException(String.format(
                        "Error: The method '%s' is specified more than once in the strategy configuration: %s. Each method should appear only once.",
                        method, STRATEGY));
                }
                STRATEGIES.put(method, new Tuple<>(strategy, getVars(strategy)));
            }
        }
        suffix_output_original_color = String.format("_%stransitions", type.toString().toLowerCase());
        suffix_merged_epa_cepa = String.format("_merge_epa_%s.dot", type.toString().toLowerCase());
    }

    // private void loadStrategy() {
    //     try {
    //         String configPath = new File("config.properties").getAbsolutePath();
    //         File configFile = new File(configPath);
    //         if (!configFile.exists())
    //         {
    //             System.out.println("config.properties file not found at: " + configPath);
    //             return;
    //         }
    //         Properties prop = new Properties();
    //         try (InputStream input = new java.io.FileInputStream(configFile)) {
    //             prop.load(input);
    //         }

    //         STRATEGIES_ON = prop.getProperty("strategy_on") != null && (prop.getProperty("strategy_on").equals("true") || prop.getProperty("strategy_on").equals("on"));
    //         STRATEGY = prop.getProperty("strategy") != null ? prop.getProperty("strategy") : "";
    //         if (STRATEGIES_ON) {
    //             SENDER_STRATEGY = prop.getProperty("sender") != null ? prop.getProperty("sender") : "";
    //         }
    //     } catch (IOException ex) {
    //         ex.printStackTrace();
    //     }
    // }

    private static List<String> getVars(String input) {
        List<String> words = new ArrayList<>();
        Pattern pattern = Pattern.compile("\\b[a-zA-Z._]+\\b");
        Matcher matcher = pattern.matcher(input);

        while (matcher.find()) {
            String var = matcher.group().strip();
            if (!var.equals("and"))
                words.add(matcher.group());
        }
        return words;
    }

    public EPA buildJustEPA() throws InterruptedException, ExecutionException, IOException {
        var before = LocalDateTime.now();
        EPA epa = new EPA(this.originalAlloyFile);
        epa.buildFullEPA();
        LocalDateTime after = LocalDateTime.now();
        long tiempo_total = Duration.between(before, after).getSeconds();
        System.out.println("EPA cost(seconds): " + tiempo_total + "\n");
        this.alloyFileCopy = epa.alloyFileCopy;
        return epa;
    }

    public abstract void buildFullEPA() throws InterruptedException, ExecutionException, IOException;

    public void buildCEPA(String dot_epa_original) throws InterruptedException, ExecutionException, IOException {
        if (!new File(this.alloyFileCopy).exists()) {
            throw new RuntimeException("File %s does not exists. Make sure this file is the copy of original alloy model.");
        }
        LocalDateTime before = LocalDateTime.now();
        createAlloyColorTransitionsFile(dot_epa_original, CEPA.SCOPE);
        super.buildFullEPA();
        LocalDateTime after = LocalDateTime.now();
        long tiempo_total = Duration.between(before, after).getSeconds();
        System.out.printf("%s cost(seconds): %s%n\n", this.type.toString().replace("SUPERBLUE", "Hyper-MUST").replace("BLUE","MUST"), tiempo_total);
    }

    protected abstract void createAlloyColorTransitionsFile(String dot_file_path_bepa, String scope) throws IOException;

    @Override
    public void writeParsedFile() throws IOException {
        Set<Transition> t_epa = Transition.readTransitionsFromDotFile(dot_epa_reachable);
        Transition[] transitions_epa = new Transition[t_epa.size()];
        t_epa.toArray(transitions_epa);
        Set<Transition> transitions_bepa = Transition.readTransitionsFromDotFile(this.path_dot_transitions);

        Set<Transition> new_transitions = new HashSet<>();

        // Replace transitions with the color
        for (Transition t_old : transitions_epa) {
            String actionName = t_old.action();
            for (int j = 0; j < t_old.finalState().size(); ++j) {
                for (Transition t_new : transitions_bepa) {
                    boolean sameAction = actionName.equals(t_new.action());
                    boolean sameInitialState = t_old.initialState().equals(t_new.initialState());
                    if (!sameAction || !sameInitialState) {
                        continue;
                    }
                    for (Tuple<String, String> endStates_new : t_new.finalState()) {
                        String endState_old = t_old.finalState().get(j).first();
                        String endColorState_old = t_old.finalState().get(j).second();
                        boolean sameEndState = endState_old.equals(endStates_new.first());
                        //Blue transition must not be replaced
                        String mustColor = AEPA.TYPE.BLUE.getColor();
                        String mayColor = TYPE.CLASSIC.getColor();
                        String transition_color_new = endStates_new.second();
                        if (sameEndState) {
                            //option 1. black transition. replace
                            if (endColorState_old.equals(mayColor)) {
                                t_old.finalState().get(j).setSecond(transition_color_new);
                            }
                            //option 2: semimust transition: dont replace. add new transition
                            else if (!endColorState_old.equals(mustColor) && !endColorState_old.equals(transition_color_new)){
                                new_transitions.add(t_new);
                            }
                            //option 3: must transition. dont replace. do nothing
                        }
                    }
                }
            }
        }

        GraphvizUtils graphviz = new GraphvizUtils();
        //Write parsed file
        this.path_dot_epa_parsed = this.alloyFileCopy.replace(".als", suffix_output_original_color + EPA.suffix_output_parsed + ".dot");
        new_transitions.addAll(List.of(transitions_epa));
        List<Transition> compact = Transition.compactActions(new_transitions);
        graphviz.writeDotFile(this.path_dot_epa_parsed, this.state_names_path, compact);

        //Merge original dot epa and original bepa
        this.path_merge_dot = this.alloyFileCopy.replace(".als", suffix_merged_epa_cepa);
        graphviz.writeDotFile(this.path_merge_dot, new_transitions);

        //Graph with cluster: used the merged file
//        SubGraph subGraph = new SubGraph(this.path_merge_dot, true);
//        Set<Transition> transitions = Transition.readTransitionsFromDotFile(this.path_merge_dot);
//        graphviz.writeDotFile(this.alloyFileCopy.replace(".als", "_cluster.dot"), this.state_names_path, transitions, subGraph);

        if (this.type.equals(TYPE.SUPERBLUE)) {
            String forked_and_parsed_dot_path = this.path_dot_epa_parsed.replace(suffix_output_original_color + EPA.suffix_output_parsed + ".dot", "forked_arrows.dot");
            graphviz.writeDotFileForkedArrows(this.path_dot_epa_parsed, forked_and_parsed_dot_path);
        }

        GraphvizUtils.resetQueriesNotAvailable();
    }


}
