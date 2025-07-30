package ar.uba.dc.EPA;

import ar.uba.dc.config.Config;
import ar.uba.dc.query.AlloyFuncs;

import java.io.IOException;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;
import java.util.List;
import java.util.concurrent.ExecutionException;

public class SBEPA extends CEPA {

    public static Deque<String> COLORS_STACK;
    public static final List<String> FIXED_COLORS = Arrays.asList(TYPE.SUPERBLUE.getColor(), "blueviolet", "chartreuse", "darkgoldenrod1", "crimson", "deeppink", "aqua", "darkgreen", "darkgoldenrod1", "gold3", "green");

    static {
        COLORS_STACK = new ArrayDeque<>(FIXED_COLORS);
    }

    public static void resetFixedColors() {
        COLORS_STACK = new ArrayDeque<>(FIXED_COLORS);
    }

    public double[] TIMES = {0, 0, 0};

    public SBEPA(String alloy_file) {
        super(TYPE.SUPERBLUE, alloy_file, false, "_originalsuperblue", FIXED_COLORS.stream().map(e -> e + "_transition_").toList());
    }

    public void buildFullEPA() throws InterruptedException, ExecutionException, IOException {
        LocalDateTime before = LocalDateTime.now();
        EPA epa = this.buildJustEPA();
        LocalDateTime after = LocalDateTime.now();
        TIMES[0] = Duration.between(before, after).toMillis() / 1000.0;

        BEPA bepa = new BEPA(this.originalAlloyFile);
        bepa.dot_epa_reachable = epa.path_dot_reachable;
        before = LocalDateTime.now();
        bepa.buildCEPA(epa.path_dot_transitions);
        after = LocalDateTime.now();
        TIMES[1] = Duration.between(before, after).toMillis() / 1000.0;

        this.dot_epa_reachable = bepa.path_merge_dot;
        before = LocalDateTime.now();
        this.buildCEPA(bepa.path_merge_dot);
        after = LocalDateTime.now();
        TIMES[2] = Duration.between(before, after).toMillis() / 1000.0;
        // If config.ini updated timeout, refresh the value
        Config.QUERY_TIMEOUT_LIMIT_IN_SECS = Config.QUERY_TIMEOUT_LIMIT_IN_SECS_COPY;
    }

    protected void createAlloyColorTransitionsFile(String dot_file_path_bepa, String scope) throws IOException {
        AlloyFuncs alloyFuncs = new AlloyFuncs(this.alloyFileCopy);
        alloyFuncs.writeTurquoisePredTransitionsInAlloyFile(dot_file_path_bepa, scope);
    }
}
