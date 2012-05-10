import java.util.LinkedList;


// Minimal contained class
class Contained {
	int value;
	
	public Contained (int value) {
		this.value = value;
	}
}

public class ForAllExtended {

	//@ requires (\forall Contained c; a.contains(c) && b.contains(c); 1 < c.value && c.value < 4);
	public static /*@ pure @*/ void forAllExtended(LinkedList<Contained> a, LinkedList<Contained> b){
		// Do nothing
	}
	
	public static void main(String[] args) {
		LinkedList<Contained> A = new LinkedList<Contained>();
		LinkedList<Contained> B = new LinkedList<Contained>();
		LinkedList<Contained> C = new LinkedList<Contained>();
		
		Contained cA = new Contained (1);
		Contained cB = new Contained (2);
		Contained cC = new Contained (3);
		Contained cD = new Contained (4);
		
		// Precondition should hold
		System.out.println("Precondition holds!");
		
		A.add(cA);
		A.add(cB);
		A.add(cC);
		
		B.add(cB);
		B.add(cC);
		B.add(cD);
		
		forAllExtended(A, B);
		
		// Precondition should fail
		System.out.println("Precondition fails!");		
		
		C.add(cA);
		C.add(cB);
		C.add(cC);
		C.add(cD);
		
		forAllExtended(A, C);
	}

}
