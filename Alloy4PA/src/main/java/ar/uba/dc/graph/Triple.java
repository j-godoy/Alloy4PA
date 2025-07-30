package ar.uba.dc.graph;

public class Triple<A, B, C> {
    private final A first;
    private final B second;
    private final C third;

    public Triple(A first, B second, C third) {
        this.first = first;
        this.second = second;
        this.third = third;
    }
    public A first() {
        return first;
    }
    public B second() {
        return second;
    }
    public C third() {
        return third;
    }

    public String toString() {
        return first + "," + second + "," + third;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Triple<?, ?, ?> triple = (Triple<?, ?, ?>) o;

        if (!first.equals(triple.first)) return false;
        if (!second.equals(triple.second)) return false;
        return third.equals(triple.third);
    }

    @Override
    public int hashCode() {
        int result = first.hashCode();
        result = 31 * result + second.hashCode();
        result = 31 * result + third.hashCode();
        return result;
    }
}
