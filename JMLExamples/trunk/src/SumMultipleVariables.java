
public class SumMultipleVariables {
	
	// Basically says that v cannot be 0
	//@ requires 1 <= (\sum int i, j; 0 < i && i < 10 && j == i ++; j * i * v);
	public static void sumMultipleVars (int v) {
		// Do nothing
	}
	
	public static void main(String[] args) {
		System.out.println("Precondition holds!");
		sumMultipleVars(1);
		
		System.out.println("Precondition fails!");
		sumMultipleVars(0);
	}

}
