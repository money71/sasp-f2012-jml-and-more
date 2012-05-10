public class Old {
    
    public static int var = 1;
    
    //@ assignable var;
    //@ ensures var == \old(var) + 1;
    public static void foo () {
    	var++;
    }

    public static void main (String[] args){
    	foo();
    }
}