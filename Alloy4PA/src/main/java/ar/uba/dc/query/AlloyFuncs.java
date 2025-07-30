package ar.uba.dc.query;

import ar.uba.dc.EPA.AEPA;
import ar.uba.dc.EPA.BEPA;
import ar.uba.dc.EPA.SBEPA;
import ar.uba.dc.config.Config;
import ar.uba.dc.graph.GraphvizUtils;
import ar.uba.dc.graph.Transition;
import ar.uba.dc.graph.Triple;
import ar.uba.dc.graph.Tuple;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;


public class AlloyFuncs {

    private final String alloyFile;

    public AlloyFuncs(String alloy_file) {
        this.alloyFile = alloy_file;
    }

    AlloyFuncs(File alloy_file) {
        this.alloyFile = alloy_file.getAbsolutePath();
    }

    public Module parseFile() {
        // Alloy4 sends diagnostic messages and progress reports to the
        // A4Reporter.
        // By default, the A4Reporter ignores all these events (but you can
        // extend the A4Reporter to display the event for the user)
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override
            public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                System.out.flush();
            }
        };

        // Parse+typecheck the model
        System.out.println("=========== Parsing+Typechecking " + this.alloyFile + " =============");
        return CompUtil.parseEverything_fromFile(rep, null, this.alloyFile);
    }

    public static A4Options options() {
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.SAT4J;
        options.noOverflow = true;
        return options;
    }

    public static A4Reporter rep() {
        return new A4Reporter() {

            // For example, here we choose to display each "warning" by printing
            // it to System.out
            @Override
            public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                System.out.flush();
            }
        };
    }


    public void writeBluePredTransitionsInAlloyFile(String dotfile, String scope) throws IOException {
        Module world = this.parseFile();
        Set<Transition> transitions = Transition.readTransitionsFromDotFile(dotfile);
        List<String> predsToAppend = new ArrayList<>();
        predsToAppend.add("\n\n\n//======predicates for blue queries======\n\n\n");
        for (Transition t : transitions) {
            if (Config.AVOID_MUST_ALL) {
                System.out.println("Must query: Parameter AVOID_MUST_ALL is True. Skipping all must queries.");
                continue;
            }
            if (Config.AVOID_MUST_CONSTRUCTOR && t.action().equals("constructor")) {// It usually takes a lot of time because use many arguments
                System.out.println("Must query: Parameter AVOID_MUST_CONSTRUCTOR is True. Skipping must queries for constructor.");
                continue;
            }
            if (Config.AVOID_MUST_TAU && t.action().equals("t")) { // It usually takes a lot of time
                System.out.println("Must query: Parameter AVOID_MUST_TAU is True. Skipping must queries for TAU.");
                continue;
            }
            for (Tuple<String, String> tuple : t.finalState()) {
                String nuevoPred = getBlueTransition(t.action(), t.initialState(), tuple.first(), world, scope);
                predsToAppend.add(nuevoPred);
            }
        }
        appendToFile(this.alloyFile, predsToAppend);
    }

    private void appendToFile(String path, List<String> contentLines) throws IOException {
        FileWriter fileWriter = new FileWriter(path, true);
        PrintWriter printWriter = new PrintWriter(fileWriter);
        contentLines.forEach(printWriter::println);
        fileWriter.close();
    }

    public void writeTurquoisePredTransitionsInAlloyFile(String dotfile, String scope) throws IOException {
        Module world = this.parseFile();
        Set<Transition> transitions = Transition.readTransitionsFromDotFile(dotfile);
        List<String> predsToAppend = new ArrayList<>();
        predsToAppend.add("\n\n\n//======predicates for turquoise queries======\n\n\n");
        for (Transition t : transitions) {
            if (Config.AVOID_MUST_CONSTRUCTOR && t.action().equals("constructor")) { // It usually takes a lot of time because use many arguments
                System.out.println("Hyper-Must query: Parameter AVOID_MUST_CONSTRUCTOR is True. Skipping must queries for constructor.");
                continue;
            }
            if (Config.AVOID_MUST_TAU && t.action().equals("t")) { // It usually takes a lot of time
                System.out.println("Hyper-Must query: Parameter AVOID_MUST_TAU is True. Skipping must queries for TAU.");
                continue;
            }
            String colorBlue = AEPA.TYPE.BLUE.getColor();
            String colorRed = AEPA.TYPE.RED.getColor();
            List<List<String>> toStatesCombination = t.toStatesCombination();

            // Only check for the first combination (we don't want to have so many colors for transitions)
            // example: if from state A reach states Q1, Q2, Q3, Q4 by "f", then i want to check if the union
            // of 2 of them are "turquoise". If not, then we check the 3 transitions and finally for all transitions.
//            combinations.sort((list1, list2) -> Integer.compare(list2.size(), list1.size()));
//            int initialCount = toStatesCombination.isEmpty() ? 0 : toStatesCombination.get(0).size();
            List<List<String>> semiMustOutgoingStates = new ArrayList<>();
            for (List<String> comb : toStatesCombination) {
                // If at least one of the outgoing states is reachable by a blue transition, then skip this one
                // same if one transition is red (so it is not enable)
                if (t.finalState().stream().anyMatch(e->(e.second().equals(colorBlue) || e.second().equals(colorRed)) && comb.stream().anyMatch(s->s.equals(e.first())))) {
                    continue;
                }
                //if the current combinations of outgoing states already include "colored" states,
                // then skip because obviusly the formula with be unsatisfiable if we add more states
                if (semiMustOutgoingStates.stream().anyMatch(comb::containsAll)) {
                    continue;
                }
//                if (initialCount < comb.size() && SBEPA.COLORS_STACK.size() != SBEPA.FIXED_COLORS.size()) {
//                    break;
//                }
                String newPred = getColorTransition(t.action(), t.initialState(), comb, world, scope);
                if (newPred.isEmpty()) // empty means the transition does not exists for any parameter
                    continue;
                String color = SBEPA.COLORS_STACK.peek();
                Boolean satisfiable = false;
                if (!AlloyFuncs.isSat(this.alloyFile, newPred, getNamePredToRun("met_"+t.action(), t.initialState(), comb, color), satisfiable)){
                    semiMustOutgoingStates.add(comb);
                    SBEPA.COLORS_STACK.pop();
                    predsToAppend.add(newPred);
                }
            }
            SBEPA.resetFixedColors();
        }
        appendToFile(this.alloyFile, predsToAppend);
    }

    public static boolean isSat(String alloyFile, String predsToAppend, String namePredToRun, Boolean satisfiable) throws IOException {
        File tmpAls = new File(alloyFile);
        boolean appendToFile = !predsToAppend.isBlank();
        if (appendToFile) {
            String run = predsToAppend + "\n";
            tmpAls = CompUtil.flushModelToFile(run, null);
        }
        AlloyFuncs alloyFuncs = new AlloyFuncs(tmpAls);
        List<String> lines = Files.readAllLines(Paths.get(alloyFile), StandardCharsets.UTF_8);

        if (appendToFile) {
            alloyFuncs.appendToFile(tmpAls.getAbsolutePath(), lines);
        }

        Module world = alloyFuncs.parseFile();
        for (Command command : world.getAllCommands()) {
            if (!command.label.equals(namePredToRun))
                continue;


            //FIX: duplicated code
            LocalDateTime before = LocalDateTime.now();
            ExecutorService executor = Executors.newSingleThreadExecutor();
            Callable<A4Solution> task = () -> TranslateAlloyToKodkod.execute_command(AlloyFuncs.rep(), world.getAllReachableSigs(), command, AlloyFuncs.options());
            Future<A4Solution> future = executor.submit(task);
            Boolean rta;
            try {
                A4Solution ans = future.get(Config.QUERY_TIMEOUT_LIMIT_IN_SECS, TimeUnit.SECONDS);
                rta = ans.satisfiable();
            } catch (InterruptedException | ExecutionException e) {
                throw new RuntimeException(e);
            } catch (TimeoutException e) {
                rta = satisfiable;
                String query = namePredToRun.replaceAll("__", "_").replaceAll("_a_","_to_").replaceAll("_mediante_","_by_").replaceAll("_met_","_").trim();
                query = query.replace("superblue_transition","hypermust_transition");
                query = query.replace("blue_transition","must_transition");
                System.out.println("TO with pred " + query);
                QueryProcessor.syncList.add(new Triple<>(command.label, -1.0, rta));
            } finally {
                future.cancel(true);
                executor.shutdown();
            }

            LocalDateTime after = LocalDateTime.now();
            double total_time = Duration.between(before, after).toMillis() / 1000.0;
            QueryProcessor.syncList.add(new Triple<>(command.label, total_time, rta));

            return rta;
        }
        throw new RuntimeException("Pred " + namePredToRun + " does not exist. Pred:\n"+predsToAppend);
    }

    public String getBlueTransition(String funcName, String is, String fs, Module world, String scope) {
        Func from = getPred(world, is);
        Func to = getPred(world, fs);
        Func action = getPred(world, funcName);
        return createColorTransition(action, from, new ArrayList<>(List.of(to)), AEPA.TYPE.BLUE.getColor(), scope);
    }

    public String getColorTransition(String funcName, String is, List<String> fe, Module world, String scope) {
        Func from = getPred(world, is);
        List<Func> to = fe.stream().map(e->getPred(world, e)).collect(Collectors.toList());
        Func action = getPred(world, funcName);
        return createColorTransition(action, from, to, SBEPA.COLORS_STACK.peek(), scope);
    }

    private String getNamePredToRun(String funcName, String from, List<String> fe, String color) {
        from = from.replace("partition", "");
        final StringJoiner stringJoiner = new StringJoiner("_");
        fe.forEach(e->stringJoiner.add(e.replace("partition","")));
        return String.format("%s_transition__%s__a__%s__mediante_%s", color, from, stringJoiner, funcName);
    }

    private String createColorTransition(Func f, Func state_from, List<Func> states_to, String color, String scope) {
        String from = state_from.label.replace("this/", "");
        String funcName = f.label.replace("this/", "");
        List<String> predsNamesTo = states_to.stream().map(e->e.label.replace("this/", "")).collect(Collectors.toList());
        Tuple<String, String> predicateNotBlueTransition = predicateNotBlueTransition(f, from, predsNamesTo);

        String predName = getNamePredToRun(funcName, from, predsNamesTo, color);

        String existPred = makePred(predName, predicateNotBlueTransition.first(), scope);
        boolean transitionExist;
        try {
            Boolean satisfiable = true;
            transitionExist = !BEPA.STRATEGIES_ON || BEPA.STRATEGIES.isEmpty() || isSat(this.alloyFile, existPred, predName, satisfiable);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        String newPred = "";
        if (transitionExist) {
            newPred = makePred(predName, predicateNotBlueTransition.second(), scope);
        } else {
            //Saving not enable transition to be displayed as grey/red transitions
            Transition t = new Transition(predName);
            //TODO: is it necessary the condition?
            if (t.finalState().size() == 1) {
                GraphvizUtils.queriesNotAvailable.add(t);
                System.out.println("Transition RED:" + new Transition(predName));
                System.out.println("Transition RED pred:\n" + existPred);
            }
        }

        return newPred;
    }

    private String makePred(String predName, String formula, String scope) {
        String ret = String.format("pred %s {\n", predName);
        ret += String.format("\t%s\n", formula);
        ret += "}\n";

        // I look for the bound for EstadoConcreto. I check how many are needed at least.
        // To do this, I count how many 'somex' or 'somex,y' appear.
        // If the scope bound is less than the number of 'x' and 'y', I replace it with that count + 1.
        String simpleSome = "somex:";
        String twiceSome = "somex,y";
        String tmpFormula = formula.replace(" ", ""); //To avoid possible extra spaces
        int statesCount = countAp(tmpFormula, simpleSome) + countAp(tmpFormula, twiceSome)*2;
        Pattern pattern = Pattern.compile("(\\d+)\\s+EstadoConcreto");
        Matcher matcher = pattern.matcher(scope);

        if (matcher.find()) {
            String numberStr = matcher.group(1);
            int curr_numberState = Integer.parseInt(numberStr);
            if (curr_numberState < statesCount) {
                System.out.println("Updating SCOPE: '" + scope +"' by ");
                scope = matcher.replaceFirst(statesCount+" EstadoConcreto");
                System.out.println("New SCOPE: '" + scope+"'");
            }
        }
        ret += String.format("run %s for %s\n", predName, scope);
        return ret;
    }

    private int countAp(String formula, String search) {
        int count = 0;
        int indice = formula.indexOf(search);
        while (indice >= 0) {
            count++;
            indice = formula.indexOf(search, indice + 1);
        }
        return count;
    }

    public Tuple<String, String> predicateNotBlueTransition(Func f, String from, List<String> to_partitions) {
        String action = f.label.replace("this/", "");

        String actionOriginalName = action.replace("met_", "");
        String strategy = "";
        List<String> userDefinedVars = new ArrayList<>();
        if (BEPA.STRATEGIES.containsKey(actionOriginalName)) {
            strategy = BEPA.STRATEGIES.get(actionOriginalName).first();
            userDefinedVars = BEPA.STRATEGIES.get(actionOriginalName).second();
        }

        StringJoiner typesDeclaration = new StringJoiner(", ");
        StringJoiner fParams = new StringJoiner(", ");
        for (Decl k : f.decls) {
            if (k.expr.toString().contains("EstadoConcreto")) {
                continue;
            }
            for (ExprHasName name : k.names) {
                String paramName = name.label;
                //Vars not defined, or defined with ranges, then I need to add parameter type in forall
                if (!userDefinedVars.contains(paramName) || Collections.frequency(userDefinedVars, paramName) > 1) {
                    if (!paramName.equals("sender") || BEPA.SENDER_STRATEGY.isBlank() || BEPA.SENDER_STRATEGY.startsWith("!")) {
                        String curr = paramName + ":" + k.expr.type();
                        typesDeclaration.add(curr);
                        fParams.add(paramName);
                    } else { //if the paramName is sender and there is a strategy for sender in config, then use this.
                        fParams.add(BEPA.SENDER_STRATEGY); //TODO it only accept a fixed sender value. maybe could be useful use something like sender != .... and ....
                    }

                } else {
                    // If parameter is defined once time, then use this value and remove this from strategy string
                    String pat = "(" + paramName + "\\s*=\\s*)(\\w*[._]*\\w*)(\\s*)";
                    Pattern pattern = Pattern.compile(pat);
                    Matcher matcher = pattern.matcher(strategy);
                    if (matcher.find()) {
                        String value = matcher.group(2).strip();
                        fParams.add(value);
                        strategy = strategy.replace(matcher.group(), "");
                    } else {
                        pat = "(" + paramName + "\\s*!=\\s*)(\\w*[._]*\\w*)(\\s*)";
                        pattern = Pattern.compile(pat);
                        matcher = pattern.matcher(strategy);
                        if (matcher.find()) {
                            String curr = paramName + ":" + k.expr.type();
                            typesDeclaration.add(curr);
                            fParams.add(paramName);
                        } else {
                            throw new RuntimeException(String.format("bug? parameter '%s' should be defined?", paramName));
                        }
                    }
                }
            }
        }
        StringJoiner strategyJoin = getStringJoiner(strategy);

        if (!strategy.isBlank() || BEPA.SENDER_STRATEGY.startsWith("!")) {
            strategy = "and " + strategyJoin + " ";
        }

        int initial_size = 2; //ein, eout EstadoConcreto parameters
        String notEnabled = String.format("not pre_%s[x] or ", actionOriginalName);
        notEnabled = actionOriginalName.equals("constructor") ? "" : notEnabled;

        String enabled = String.format("pre_%s[x] and ", actionOriginalName);
        enabled = actionOriginalName.equals("constructor") ? "" : enabled;

        String not_to_states = getNotReachableToStates(to_partitions, "y");

        StringJoiner exists = new StringJoiner("\n");
        String forall;
        if (typesDeclaration.length() > initial_size) {
            for (String s : to_partitions) {
                String e = "some x, y: EstadoConcreto | %s[x] and (%s(some %s | pre_params_%s[x,%s] %sand %s[x,y,%s] and %s[y]))";
                e = String.format(e, from, enabled, typesDeclaration, actionOriginalName, fParams, strategy, action, fParams, s);
                exists.add(e);
            }

            forall = "some x: EstadoConcreto | %s[x] and (%s(all %s | pre_params_%s[x,%s] %simplies some y:EstadoConcreto | %s[x,y,%s] and not %s))";
            forall = String.format(forall, from, notEnabled, typesDeclaration, actionOriginalName, fParams, strategy, action, fParams, not_to_states);
        } else {
            for (String s : to_partitions) {
                String e = "some x,y: EstadoConcreto | %s[x] and (%s(pre_params_%s[x,%s] and %s[x,y,%s] and %s[y]))";
                e = String.format(e, from, enabled, actionOriginalName, fParams, action, fParams, s);
                exists.add(e);
            }

            forall = "some x: EstadoConcreto | %s[x] and (%s(pre_params_%s[x,%s] implies some y:EstadoConcreto | %s[x,y,%s] and not %s))";
            forall = String.format(forall, from, notEnabled, actionOriginalName, fParams, action, fParams, not_to_states);
        }
        return new Tuple<>(exists.toString(), forall);
    }

    private static StringJoiner getStringJoiner(String strategy) {
        StringJoiner strategyJoin = new StringJoiner(" and ");
        for (String cond : strategy.split(",")) {
            if (!cond.isBlank())
                strategyJoin.add(cond.strip());
        }
        //TODO: this is for strategy "!AddressA and sender != AddressB" for example. Its mandatory that it starts with "!"
        //IT doesnt work if there is a sender strategy also in BEPA.STRATEGIES.
        if (BEPA.SENDER_STRATEGY.startsWith("!")) {
            strategyJoin.add("sender !="+BEPA.SENDER_STRATEGY.substring(1));
        }
        return strategyJoin;
    }

    private String getNotReachableToStates(List<String> to, String stateVar) {
        StringJoiner joiner = new StringJoiner(" and not ");
        to.forEach(e->joiner.add(String.format("%s[%s]", e, stateVar)));
        return joiner.toString();
    }

    public Func getPred(Module world, String to_find) {
        for (Func f : world.getAllFunc()) {
            if (f.label.endsWith("met_" + to_find) || f.label.endsWith("partition" + to_find)) {
                return f;
            }
        }
        throw new RuntimeException(String.format("Predicate %s does not exists", to_find));
    }
}
