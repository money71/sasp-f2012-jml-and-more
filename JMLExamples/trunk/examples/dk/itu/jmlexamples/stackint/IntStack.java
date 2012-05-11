package dk.itu.jmlexamples.stackint;

/*
 * from http://www.risc.jku.at/education/oldmoodle/file.php/22/JML/JML2.pdf
 * 
 * this fresh also raises:
 * "warning: Entire clause will be dropped since JmlFreshExpression is not executable" ?
 */
class IntStack // V2 
{ 
private /*@ non_null @*/ int[] stack; 
private int number; 
/*@ private invariant 0 <= number 
  @ && number <= stack.length; @*/ 

/*@ private constraint 
  @ (\forall int i; 
  @ 0 <= i && i < number-1; 
  @ stack[i] == \old(stack[i])); @*/ 
private final int N = 10;

/*@ private normal_behavior 
  @ assignable stack, number; 
  @ ensures stack.length == N 
  @ && number == 0; @*/ 
public IntStack() { 
	stack = new int[N]; 
    number = 0; 
} 
/*@ private normal_behavior 
  @ assignable \nothing; 
  @ ensures \result <==> 
  @ number == 0; @*/ 
public /*@ pure @*/ boolean isempty() { 
	return number == 0; 
}

/*@ private normal_behavior 
  @ assignable stack, stack[*], number; 
  @ ensures number == \old(number)+1 
  @ && stack[number-1] == e; @*/ 
public void push(int e) { 
	if (number == stack.length) 
		resize(); 
	stack[number] = e; 
	number = number+1; 
} 

/*@ private normal_behavior 
  @ requires number > 0; 
  @ assignable number; 
  @ ensures number == \old(number)-1 
  @ && \result == stack[number]; @*/ 
public int pop(int e) 
{ number = number-1; 
return stack[number]; 
}


/*@ private normal_behavior 
  @ assignable stack; 
  @ ensures \fresh(stack) 
  @ && stack.length > 
  @ \old(stack.length) 
  @ && number == \old(number) 
  @ && (\forall int i; 
  @ 0 <= i && i < number; 
  @ stack[i] == \old(stack[i])); @*/
private void resize() { 
	int s[] = new int[2*stack.length+1]; 
	for (int i=0; i<stack.length; i++) 
		s[i] = stack[i]; 
	stack = s; 
} 
}