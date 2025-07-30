package ar.uba.dc.query;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ReduceStates {

    /**
     * @param args 1er param: path completo con nombre de archivo alloy
     *             2do param: path completo con nombre de archivo de salida
     *             3er param: #estados
     */
    public static void main(String[] args) throws IOException {

        String alloy_file = args[0];
        String output_file = args[1];
        int states = Integer.parseInt(args[2]);
        String scope = args[3];
        StringBuilder runs = new StringBuilder();
        String forDomainBound = " for " + scope;
        for (int i = 0; i <= states; ++i) {
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
            }
        }
        try (FileWriter fileWriter = new FileWriter(output_file)) {
            fileWriter.write(output_states.toString());
        }
    }

    public static String stateName(int num) {
        String ret = "S";
        if ((num + "").length() == 1)
            ret += "0" + num;
        else
            ret += num + "";
        return ret;
    }
}
