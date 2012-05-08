public static class NonNullElements {
    
    //@ requires \nonnullelements(o);
    public static void foo (Object[] o) {
	// Do nothing.
    }
}