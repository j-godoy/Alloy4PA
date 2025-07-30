package ar.uba.dc.EPA;

import ar.uba.dc.config.Config;
import ar.uba.dc.graph.GraphvizUtils;
import ar.uba.dc.graph.Transition;
import ar.uba.dc.partitioner.AlloyGenerator;
import ar.uba.dc.query.QueryProcessor;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicReference;

public abstract class AEPA {
    private final List<String> nameofPredtoRun;
    String originalAlloyFile;
    String alloyFileCopy;

    boolean satisfiable;

    String path_dot_transitions;
    String path_dot_epa_parsed;
    String path_dot_reachable;
    String suffix_output;

    public final TYPE type;

    public enum TYPE {
        BLUE("blue"), //Must
        SUPERBLUE("turquoise"), //Semi must
        CLASSIC("black"), //maybe
        RED("red"); //disable
        private final String color;
        TYPE(String color) {
            this.color = color;
        }

        public String getColor() {
            return color;
        }
    }

    String state_names_path;


    public List<Transition> transitions;

    AEPA(TYPE type, String alloy_file_path, boolean satisfiable, String suffix_output, List<String> runOnlyPredsStartingWithThisName) {
        this.type = type;
        this.originalAlloyFile = alloy_file_path;
        this.satisfiable = satisfiable;
        this.suffix_output = suffix_output;
        this.transitions = new ArrayList<>();
        this.nameofPredtoRun = runOnlyPredsStartingWithThisName;

        //Make a copy of the original file (Alloy model)
        String fileName = Paths.get(this.originalAlloyFile).getFileName().toString();
        String newDir = fileName.replace(".als", "");
        Path newPath = Path.of(Paths.get(this.originalAlloyFile).getParent().getParent().toString(), newDir, fileName);
        if (!new File(String.valueOf(newPath)).exists() || this.type.equals(TYPE.CLASSIC)) {
            try {
                Files.createDirectories(newPath.getParent());
                Files.copy(Paths.get(originalAlloyFile), newPath, StandardCopyOption.REPLACE_EXISTING);
            } catch (IOException e) {
                System.out.println(e.getMessage());
                throw new RuntimeException(e);
            }

        }
        //Replace Alloy model path for new copy
        this.alloyFileCopy = newPath.toString();

        this.state_names_path = this.alloyFileCopy.replace(".als", Config.SUFFIX_GRAPHVIZ_NAME_STATES);

    }

    private void loadConfig(String configFile) throws IOException {
        System.out.println("Loading config " + configFile);
        CEPA.resetParameters();
        List<String> lines = Files.readAllLines(Path.of(configFile));
        for (String line : lines) {
            if (line.startsWith("CantidadObjetosEnRuns") || line.toLowerCase().startsWith("scope")) {
                CEPA.SCOPE = line.split("=")[1].strip();
            }
            if (line.toLowerCase().startsWith("strategy_on")) {
                String value = line.split("=")[1].strip();
                CEPA.STRATEGIES_ON = value.equalsIgnoreCase("true") || value.equalsIgnoreCase("yes") || value.equalsIgnoreCase("on");
            }
            if (line.toLowerCase().replaceAll(" ", "").startsWith("strategy=")) {
                CEPA.STRATEGY = line.replace("strategy=","").replace("Strategy=","").replace("Strategy =","").replace("strategy =","").strip();
            }
            if (line.toLowerCase().replaceAll(" ", "").startsWith("sender=")) {
                CEPA.SENDER_STRATEGY = line.replace("sender=","").replace("Sender=","").replace("Sender =","").replace("sender =","").strip();
            }
        }
        if (!CEPA.STRATEGIES_ON) {
            if (!CEPA.SENDER_STRATEGY.isEmpty()) {
                System.out.printf("WARNING! Disabling sender strategy '%s' because strategy_on parameter is not enabled", CEPA.SENDER_STRATEGY);
                CEPA.SENDER_STRATEGY = "";
            }
        }
    }


    public void buildFullEPA() throws InterruptedException, ExecutionException, IOException {
        Path newPath = Paths.get(this.alloyFileCopy);
        if (this.type.equals(TYPE.CLASSIC)) {
            Files.createDirectories(newPath.getParent());
            Files.copy(Paths.get(originalAlloyFile), newPath, StandardCopyOption.REPLACE_EXISTING);
            //add partitions as predicates in the new File
            String config_path = Path.of(Paths.get(originalAlloyFile).getParent().toString(), Paths.get(originalAlloyFile).getFileName().toString().replace(".als", "Config.ini")).toString();
            loadConfig(config_path);
            makePreconditions(config_path);
        }

//        QueryProcessor.resetSyncList();

        int cont = 1;
        String SUFFIX = "_part";
        String filename = alloyFileCopy.split("\\.")[0] + SUFFIX + cont + "." + alloyFileCopy.split("\\.")[1];


        ExecutorService executorService = Executors.newFixedThreadPool(Config.MAX_THREAD_NUMBER);
        Collection<Callable<List<Transition>>> callables = new ArrayList<>();

        while (this.type == TYPE.CLASSIC && new File(filename).exists()) {
            callables.add(new QueryProcessor(filename, this.satisfiable, this.nameofPredtoRun));
            cont++;
            filename = alloyFileCopy.split("\\.")[0] + SUFFIX + cont + "." + alloyFileCopy.split("\\.")[1];
        }

        if (cont == 1) {
            callables.add(new QueryProcessor(this.alloyFileCopy, this.satisfiable, this.nameofPredtoRun));
        }

        List<Future<List<Transition>>> taskFutureList = executorService.invokeAll(callables);
        for (Future<List<Transition>> future : taskFutureList) {
            this.transitions.addAll(future.get());
        }
        executorService.shutdown();

        saveQueriesTime();

        this.path_dot_transitions = alloyFileCopy.replace(".als", this.suffix_output + ".dot");
        writeDotFile();
        this.path_dot_reachable = alloyFileCopy.replace(".als", this.suffix_output+"_reachable.dot");
        writeDotReachableFile();

        this.writeParsedFile();
    }


    public static void makePreconditions(String config) {
       AlloyGenerator processor = new AlloyGenerator(config);
       try {
           processor.run();
       } catch (Exception e) {
           System.err.println("Exception: " + e.getMessage());
           e.printStackTrace();
           System.exit(2);
       }
    }


    public abstract void writeParsedFile() throws IOException;

    public void writeDotFile() throws IOException {
        GraphvizUtils gu = new GraphvizUtils();
        gu.writeDotFile(this.path_dot_transitions, this.transitions);
    }

    public void writeDotReachableFile() throws IOException {
        GraphvizUtils gu = new GraphvizUtils();
        gu.writeDotFileReachable(this.path_dot_reachable, Transition.getReachableTransitions("S00", this.transitions));
    }

    public void saveQueriesTime() throws IOException {
        AtomicReference<Double> sum = new AtomicReference<>(0.0);
        AtomicReference<Double> max = new AtomicReference<>(0.0);
        AtomicReference<Double> min = new AtomicReference<>(Double.MAX_VALUE);
        AtomicReference<Integer> time_outs = new AtomicReference<>(0);
        QueryProcessor.syncList.forEach(i -> sum.updateAndGet(v -> i.second() >= 0 ? v + i.second() : v));
        QueryProcessor.syncList.forEach(i -> time_outs.updateAndGet(v -> i.second() < 0 ? v + 1 : v));
        QueryProcessor.syncList.forEach(i -> max.updateAndGet(m -> i.second() >= 0 && i.second() > m ? i.second() : m));
        QueryProcessor.syncList.forEach(i -> min.updateAndGet(m -> i.second() >= 0 && i.second() < m ? i.second() : m));

        int total_queries = QueryProcessor.syncList.size()-time_outs.get();
        double avg = total_queries > 0 ? sum.get() / total_queries : 0;
        String statistics = "Metric" + "," + this.type.name() + "\n" +
                "total_queries" + "," + total_queries + "\n" +
                "max_time(secs)" + "," + max + "\n" +
                "min_time(secs)" + "," + min + "\n" +
                "avg_time(secs)" + "," + avg + "\n" +
                "total_time_outs" + "," + time_outs + "\n" +
                "total_time(secs)" + "," + sum;

        writeFile(this.alloyFileCopy.replace(".als", "_queriesTime_" + this.type.name() + ".csv"), statistics);

        StringBuilder queries = new StringBuilder();
        queries.append("Transition, Time (secs), Satisfiable\n");
        QueryProcessor.syncList.forEach(e -> queries.append(e.toString()).append("\n"));
        writeFile(this.alloyFileCopy.replace(".als", "_queriesTime_" + this.type.name() + "_raw.csv"), queries.toString());

        QueryProcessor.resetSyncList();
    }

    public void writeFile(String path, String content) throws IOException {
        FileWriter file = new FileWriter(path);
        PrintWriter pw = new PrintWriter(file);
        pw.println(content);
        file.close();
    }
}
