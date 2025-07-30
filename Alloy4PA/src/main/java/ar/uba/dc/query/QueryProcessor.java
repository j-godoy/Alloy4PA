package ar.uba.dc.query;

import ar.uba.dc.EPA.SBEPA;
import ar.uba.dc.config.Config;
import ar.uba.dc.graph.Transition;
import ar.uba.dc.graph.Triple;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.time.Duration;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.*;


public class QueryProcessor implements Callable<List<Transition>> {

    private final List<String> nameofPredtoRun;
    List<Transition> validTransitions;
    String alloy_file;
    boolean satisfiable;

    /**
     * save queries time in a concurrent context
     */
    public static volatile List<Triple<String, Double, Boolean>> syncList = Collections.synchronizedList(new ArrayList<>(300));


    /**
     * @param alloy_file  alloy file path
     * @param satisfiable if true, then dd a transition only if the query is satisfiable.
     *                    if false, then add a transition only if the query is Unsatisfiable
     * @param nameofPredtoRun the starting name of the alloy preds to run to get transitions
     */
    public QueryProcessor(String alloy_file, boolean satisfiable, List<String> nameofPredtoRun) {
        this.alloy_file = alloy_file;
        this.validTransitions = new ArrayList<>(50);
        this.satisfiable = satisfiable;
        this.nameofPredtoRun = nameofPredtoRun;
    }

    public static void resetSyncList() {
        syncList = Collections.synchronizedList(new ArrayList<>(300));
    }

    @Override
    public List<Transition> call() {

        AlloyFuncs alloyFuncs = new AlloyFuncs(this.alloy_file);
        Module world = alloyFuncs.parseFile();

        for (Command command : world.getAllCommands()) {
            //Just execute those predicates that start with "transicion_" or "bluetransition"
            if (this.nameofPredtoRun.stream().noneMatch(command.label::startsWith))
                continue;


            //hyper-must have been already processed, so avoid to re-process
            if (SBEPA.FIXED_COLORS.stream().anyMatch(command.label::startsWith))
            {
                Transition t = new Transition(command.label);
                validTransitions.add(t);
                continue;
            }

            LocalDateTime before = LocalDateTime.now();
            String query = command.label.replaceAll("__", "_").replaceAll("_a_","_to_").replaceAll("_mediante_","_by_").replaceAll("_met_","_").trim();
            query = query.replace("superblue_transition","hypermust_transition");
            query = query.replace("blue_transition","must_transition");
            if (Config.VERBOSE) {
                System.out.println("running... " + query);
            }
            ExecutorService executor = Executors.newSingleThreadExecutor();
//            Callable<A4Solution> task = () -> TranslateAlloyToKodkod.execute_command(AlloyFuncs.rep(), world.getAllReachableSigs(), command, AlloyFuncs.options());
            // Sometimes TranslateAlloyToKodkod.execute_command fails in runtime, but re-trying could execute normally
            int maxRetries = 3;
            Callable<A4Solution> task = () -> {
                int attempt = 0;
                while (true) {
                    try {
                        return TranslateAlloyToKodkod.execute_command(
                                AlloyFuncs.rep(),
                                world.getAllReachableSigs(),
                                command,
                                AlloyFuncs.options()
                        );
                    } catch (RuntimeException e) {
                        attempt++;
                        if (attempt >= maxRetries) {
                            throw e; // no más intentos...
                        }
                        System.err.println("Attempt " + attempt + " failed, retrying...");
                    }
                }
            };

            Future<A4Solution> future = executor.submit(task);
            boolean rta;
            String TO = "";
            try {
                A4Solution ans = future.get(Config.QUERY_TIMEOUT_LIMIT_IN_SECS, TimeUnit.SECONDS);
                rta = ans.satisfiable();
            } catch (InterruptedException | ExecutionException e) {
                System.out.println(e.getMessage());
                throw new RuntimeException(e);
            } catch (TimeoutException e) {
                rta = this.satisfiable;
                syncList.add(new Triple<>(command.label, -1.0, rta));
                TO = " - TO!";
            } finally {
                future.cancel(true);
                executor.shutdown();
            }

            LocalDateTime after = LocalDateTime.now();
            double total_time = Duration.between(before, after).toMillis() / 1000.0;

            syncList.add(new Triple<>(command.label, total_time, rta));

            // If satisfiable...
            boolean add = this.satisfiable == rta;
            if (add) {
                Transition t = new Transition(command.label);
                validTransitions.add(t);
            }
            if (Config.VERBOSE) {
                System.out.println(query + ": " + total_time + " - sat? " + rta + TO);
            }
        }

        return this.validTransitions;
    }
}
