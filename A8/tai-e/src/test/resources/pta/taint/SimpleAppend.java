class SimpleAppend {
    public static void main(String[] args) {
        stringAdd();
    }
    static void stringAdd() {
        String taint = SourceSink.source();
        String s = "abc" + taint + "xyz";
        SourceSink.sink(s);
    }
}