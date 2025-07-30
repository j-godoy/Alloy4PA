package ar.uba.dc.EPA;

import ar.uba.dc.query.AlloyFuncs;

import java.io.IOException;
import java.util.*;
import java.util.concurrent.ExecutionException;

public class BEPA extends CEPA {

    BEPA(String alloy_file) {
        super(TYPE.BLUE, alloy_file, false, "_originalblue", List.of("blue_transition_"));
    }

    @Override
    public void buildFullEPA() throws InterruptedException, ExecutionException, IOException {
        EPA epa = this.buildJustEPA();
        this.dot_epa_reachable = epa.path_dot_reachable;
        this.buildCEPA(epa.path_dot_transitions);
    }


    protected void createAlloyColorTransitionsFile(String dot_file_path, String scope) throws IOException {
        AlloyFuncs alloyFuncs = new AlloyFuncs(this.alloyFileCopy);
        alloyFuncs.writeBluePredTransitionsInAlloyFile(dot_file_path, scope);
    }

}
