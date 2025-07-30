package ar.uba.dc.EPA;

import ar.uba.dc.config.Config;
import ar.uba.dc.graph.GraphvizUtils;
import ar.uba.dc.graph.Transition;


import java.io.*;
import java.util.List;

public class EPA extends AEPA {
    static String suffix_output_original = "_original";
    static String suffix_output_parsed = "_parsed";

    public EPA(String original_file_path) {
        super(TYPE.CLASSIC, original_file_path, true, suffix_output_original, List.of("transition_"));
    }

    public void writeParsedFile() throws IOException {
        if (!new File(this.state_names_path).exists()) {
//            if (Config.VERBOSE) {
//                System.out.println("Not parsing because does not exist file: *" + Config.SUFFIX_GRAPHVIZ_NAME_STATES);
//            }
            return;
        }
        this.path_dot_epa_parsed = this.alloyFileCopy.replace(".als", suffix_output_parsed + ".dot");

        GraphvizUtils graphviz = new GraphvizUtils();
        List<Transition> reachableTransitions = Transition.getReachableTransitions("S00", Transition.readTransitionsFromDotFile(this.path_dot_transitions));
        graphviz.writeDotFile(this.path_dot_epa_parsed, this.state_names_path, Transition.compactActions(reachableTransitions));
    }


}
