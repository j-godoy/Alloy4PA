package ar.uba.dc.query;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ReduceStatesN {

    private final List<Integer> validStateNumbers;
    String alloy_file;
    String output_file;
    int statesM;
    String scope;

    /**
     *             1st param: full path with Alloy filename
     *             2nd param: full path with output filename
     *             3rd param: #states
     *             4th param: scope
     */
    public ReduceStatesN(String alloy_file, String output_file, String states, String scope) {
        this.alloy_file = alloy_file;
        this.output_file = output_file;
        this.statesM = Integer.parseInt(states);
        this.scope = scope;
        this.validStateNumbers = new ArrayList<>();
    }

    public List<Integer> getValidStateNumbers() throws IOException {
        StringBuilder runs = new StringBuilder();
        String forDomainBound = " for " + scope;
        for (int i = 0; i <= statesM; ++i) {
            String stateName = stateName(i);
            runs.append(String.format("run partition%s%s\n", stateName, forDomainBound));
        }

        File tmpAls = CompUtil.flushModelToFile(runs.toString(), null);
        try (
                FileWriter fileWriter = new FileWriter(tmpAls, true);
                PrintWriter printWriter = new PrintWriter(fileWriter)) {
            List<String> lines = Files.readAllLines(Paths.get(alloy_file), StandardCharsets.UTF_8);
            for (String l : lines) {
                printWriter.write(l + "\n");
            }
        }

        AlloyFuncs alloyFuncs = new AlloyFuncs(tmpAls);
        Module world = alloyFuncs.parseFile();
        StringBuilder output_states = new StringBuilder();
        for (Command command : world.getAllCommands()) {
            //Just execute those predicates that start with partitionS
            if (!command.label.startsWith("partitionS"))
                continue;


            A4Solution ans = TranslateAlloyToKodkod.execute_command(AlloyFuncs.rep(), world.getAllReachableSigs(), command, AlloyFuncs.options());
            if (ans.satisfiable()) {
                String pat = "partitionS[0-9]*";
                Pattern pattern = Pattern.compile(pat);
                Matcher matcher = pattern.matcher(command.toString());
                if (!matcher.find())
                    throw new RuntimeException(command.toString());
                int stateNumber = Integer.parseInt(matcher.group().strip().replace("partitionS", ""));
                output_states.append(stateNumber).append("\n");
                validStateNumbers.add(stateNumber);
            }
        }
        try (FileWriter fileWriter = new FileWriter(output_file)) {
            fileWriter.write(output_states.toString());
        }

        return validStateNumbers;
    }


    public String stateName(int num) {
        String ret = "S";
        if ((num + "").length() == 1)
            ret += "0" + num;
        else
            ret += num + "";
        return ret;
    }
}
