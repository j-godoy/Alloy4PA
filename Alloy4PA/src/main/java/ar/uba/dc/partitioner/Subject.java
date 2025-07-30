package ar.uba.dc.partitioner;

public class  Subject {
    String inv;
    int states;
    String pathFile;
    String nombreParticion;
    String cantidadObjetosEnRuns;
    String epa;
    String predicate;
    int dividirEstadosPor;

    public Subject(String inv, int states, String pathFile, String nombreParticion,
                   String cantidadObjetosEnRuns, String epa, String predicate, int dividirEstadosPor) {
        this.inv = inv;
        this.states = states;
        this.pathFile = pathFile;
        this.nombreParticion = nombreParticion;
        this.cantidadObjetosEnRuns = cantidadObjetosEnRuns;
        this.epa = epa;
        this.predicate = predicate;
        this.dividirEstadosPor = dividirEstadosPor;
    }

}
