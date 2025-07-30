package ar.uba.dc.graph;

public class Tuple<A, B> {
    private A first;
    private B second;

    public Tuple(A first, B second) {
        this.first = first;
        this.second = second;
    }

    public A first() {
        return first;
    }

    public B second() {
        return second;
    }

    public void setFist(A newFirst) {
        this.first = newFirst;
    }
    public void setSecond(B newSecond) {
        this.second = newSecond;
    }
}
