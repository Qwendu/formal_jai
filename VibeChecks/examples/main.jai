VC :: #import "VibeChecks";
#import "Basic";


GLOBAL := 3;
GLOBAL_CONSTANT :: 3;

assignment_from_global :: ()
{
	LOCAL := GLOBAL;
}

assignment_from_global_constant :: ()
{
	LOCAL := GLOBAL_CONSTANT;
}


no_globals :: () -> int
{
	return 3;
}

using_a_global_in_transitive_calls :: ()
{
	print("Hello, Sailor");
}

Bar :: struct
{

};

main :: ()
{
	// uncomment the commented lines to see the failure reports


	VC.require(.DOES_NOT_ACCESS_GLOBALS, no_globals);
	//VC.require(.DOES_NOT_ACCESS_GLOBALS, assignment_from_global);


	VC.require(.DOES_NOT_ACCESS_GLOBALS | .GLOBAL_CONSTANTS_ARE_FINE, assignment_from_global);
	VC.require(.DOES_NOT_ACCESS_GLOBALS | .GLOBAL_CONSTANTS_ARE_FINE, assignment_from_global_constant);

	//VC.require(.DOES_NOT_ACCESS_GLOBALS, using_a_global_in_transitive_calls);
	//VC.require(.DOES_NOT_ACCESS_GLOBALS | .GLOBAL_CONSTANTS_ARE_FINE , using_a_global_in_transitive_calls); // Handling non constant procedures is more difficult!!


	no_globals();
	assignment_from_global();
	using_a_global_in_transitive_calls();
} 
