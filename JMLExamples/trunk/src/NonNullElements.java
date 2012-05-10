public class NonNullElements {
    
    //@ requires \nonnullelements(a);
    public static void foo (Object[] a) {
    	// Do nothing.
    }

    public static void main (String[] args){
    	Object[] array = new Object[1];
    	array[0] = new Object();
    	foo(array);
    }

}