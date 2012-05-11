public class ExistsMultipleVariables {

	//@ requires (\exists int i, j; 0 <= i && i < array.length && j == i++; array[i] == 1 && array[j] == 2);
	public static void existsMultipleVars (int[] array) {
		// Do nothing
	}
	
	public static void main(String[] args) {
		System.out.println("Precondition holds!");
		existsMultipleVars(new int[] {1, 2});
		
		System.out.println("Precondition fails!");
		existsMultipleVars(new int[] {0, 2});
	}

}
