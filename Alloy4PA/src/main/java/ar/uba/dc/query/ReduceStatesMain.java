package ar.uba.dc.query;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class ReduceStatesMain {

    public static List<Integer> STATES = new ArrayList<>();

    /**
     * @param args 1st param: full path with Alloy filename
     *             2nd param: full path with output filename
     *             3rd param: #states
     *             4th param: scope
     */
    public static void main(String[] args) throws IOException {

        String alloy_file = args[0];
        String output_file = args[1];
        String states = args[2];
        String scope = args[3];

        ReduceStatesN reduceStates = new ReduceStatesN(alloy_file, output_file, states, scope);
        reduceStates.getValidStateNumbers();

    }
}
