package dk.itu.jmlexamples.binsearch;

/**
 * 
 * Based java code upon the *package org.charter.jmlunitng* - specs are 
 * 'our' contribution which is pretty close to the one presented in this paper (TODO: add ref).
 * 
 * another java implementation of the bin search 
 * - http://pastebin.com/vXezvegU
 * 
 */
public class BinSearch {
	
	/*
	 * Instead of doing assignable \nothing; 
	 * add / * @ pure @ * / to the search method which implies assignable \nothing;
	 * according to the JML2 refman (pdf p. 92):
	 * Using the modifier pure on a method achieves the same effect as specifying assignable 
	 * \nothing, but does so for the methods entire specification as opposed to a single 
	 * specification-case.   
	 */
	/*@ public normal_behavior
	 @   requires array != null;
	 @   requires (\exists int i; i>=0 && i<array.length; array[i] == target);
	 @   requires (\forall int i; i>=0 && i<array.length-1; array[i] <= array[i+1]);
	 @   assignable \nothing;
	 @   ensures \result >= 0;
	 @ also public normal_behavior
	 @   requires array != null;
	 @   requires (\forall int i; i>=0 && i<array.length; array[i] != target);
	 @   assignable \nothing;
	 @   ensures \result == -1;   
	 @*/
	public static int search( int[] array, int target ) {
	 int low = 0; // The start of the search region
	 int high = array.length; // The end of the search region
	 int mid;
	 
	 // Something left to search and target not yet found
	 //while ( low <= high ) {
	 while ( low < high ) {
	   mid = (low + high) / 2 ; // Location of the mid      
	   // Determine whether the target is smaller than, greater than,
	   // or equal to the mid element
	   if ( target < array[mid]) {
	     // Target is smaller; must be in left half
	     high = mid - 1;
	   } else if ( target > array[mid] ) {
	     // Target is larger; must be in right half
	     low = mid + 1;
	   } else {
	     // Found it!!
	     return mid;
	   }
	 }
	 return -1; // nothing found
	}

	public static void main(String[] args) {
		  
		  int[] a = {1,2,3}; 
	
		  int result =  search( a, 2 );
	   System.out.println("result: " + result);
	}

}