public static class Result {
    
    //@ ensures \result == 1;
    public static int foo () {
	return(1);
    }

    public static void main (String[] args){
	foo();
    }
}