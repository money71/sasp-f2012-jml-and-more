public class NonNullElements {
    
    //@ requires \nonnullelements(o);
    public static void foo (Object[] o) {
	// Do nothing.
    }

    public static void main (String[] args){
	Object[] array = new Object[1];
	array[0] = new Object();
	foo(array);
    }
}