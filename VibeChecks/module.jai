Vibes :: enum_flags
{
	// These properties are always being handled transitively.
	//  So putting them on main is not a good idea.
	//  :transitive_vibes:
	DOES_NOT_ACCESS_GLOBALS;
	GLOBAL_CONSTANTS_ARE_FINE;
}


require :: (requirement : Vibes, procedure : $T)
#modify 
{
	// :require_checks_for_proc:
	if cast(*Type_Info,T).type != .PROCEDURE  return false, "Expected a Procedure for the procedure argument";

	return true, "";
}
{
}




is_procedure :: (ti : *Type_Info) -> bool
{
	return ti.type == .PROCEDURE;
}


#import "Basic";
#import "Compiler";

Vibe_Checker :: struct
{
	#as using base : Metaprogram_Plugin;
	message = messages;
};

get_plugin :: () -> *Metaprogram_Plugin
{
	plug := New(Vibe_Checker);
	return plug;
}


messages :: (plug : *Metaprogram_Plugin, m : *Message)
{
	using vc := cast(*Vibe_Checker, plug);
	if m.kind == .TYPECHECKED
	{
		mt := cast(*Message_Typechecked, m);
		for body : mt.procedure_bodies
		{
			check_body_for_require_constraints(vc, body.expression);
		}
	}
}


check_body_for_require_constraints :: (vc : *Vibe_Checker, body : *Code_Procedure_Body)
{
	#import "Code_Visit";
	nodes : [..] *Code_Node;
	get_recursive_nodes_breadth_first(body, *nodes);

	for nodes 
	{
		if it.kind != .PROCEDURE_CALL  continue;
		call := cast(*Code_Procedure_Call, it);

		called_procedure := cast(*Code_Procedure_Header, call.resolved_procedure_expression);
		if called_procedure == null  continue;

		if called_procedure.kind != .PROCEDURE_HEADER  continue;

		import := called_procedure.location.enclosing_load.enclosing_import;
		if import == null  continue;


		if !(import.module_name == "VibeChecks" && called_procedure.name == "require")
		{
			continue; 
		}
		
		requirement     := call.arguments_sorted[0];
		success, property := try_evaluate_to(requirement, Vibes);
		if !success
		{
			compiler_report(sprint("Expected a literal of Type % but got %", Vibes , get_type(requirement.type)), make_location(requirement), .ERROR);
			continue;
		}
		target_function := call.arguments_sorted[1];
		if target_function.kind != .IDENT
		{
			compiler_report(sprint("Expected an identifier pointing to a function but got %", target_function.kind), make_location(target_function), .ERROR);
			continue;
		}
		
		// Here the declaration has to point to a procedure
		//  This is  because ``require``'s #modify checks that only
		//  a procedure is being passed in!
		//  :require_checks_for_proc:
		header := cast(*Code_Procedure_Header, cast(*Code_Ident, target_function).resolved_declaration.expression);
		
		stack : [..] *Code_Procedure_Header;
		passed := check_function_for_property(property, header, *stack);
		if !passed
		{

			b : String_Builder;
			builder := *b;
			print(builder, "In the call graph of this procedure the property % was violated in '%'\n", property, stack[stack.count - 1].name);
			print(builder, "The function call stack looked like this\n\n");
			for < stack  print(builder, "[%] %\n", it_index, it.name);
			print(builder, "\n");
			compiler_report(builder_to_string(builder), make_location(it));
		}
		
	}

}

check_function_for_property :: (property : Vibes, header : *Code_Procedure_Header, stack_of_functions : *[..] *Code_Procedure_Header) -> passed : bool
{
	array_add(stack_of_functions, header);
	// the pop should not be defered, as only the last return is triggered on a success.

	body   := header.body_or_null;
	if body == null
	{
		if header.procedure_flags & .INTRINSIC
		{
			// right now this seems stupid but the properties might make this
			//  more complicated later.
			// 
			is_okay := true;
			if property & .DOES_NOT_ACCESS_GLOBALS  is_okay ||= true;
			if property & .SIDE_EFFECT_FREE         is_okay ||= true;
			if !is_okay 
			{
				compiler_report(tprint("intrinsic % does not pass the vibe check %", header.name, property), make_location(header), .INFO);
			}
			return is_okay;
		}
		assert(body != null, "The body of Procedure % was null", header.name);
	}

	all_nodes : [..] *Code_Node;
	get_recursive_nodes_breadth_first(body, *all_nodes);

	for all_nodes if it.kind ==
	{
	case .PROCEDURE_CALL;
	// the properties are always transitive for now
	//  :transitive_vibes:
		pc := cast(*Code_Procedure_Call, it);
		resolved := pc.resolved_procedure_expression;
		if !pc.resolved_procedure_expression
		{
			compiler_report("This procedure call does not resolve to a procedure at compile time! So we do not know which procedures might be called here. We are conservative in the Property checking so this is not allowed.", make_location(pc), .INFO);
			return false;
		}
		if resolved.kind != .PROCEDURE_HEADER  compiler_report(tprint("Expected to resolve to a procedure header, but got %", resolved.kind), make_location(resolved));
		passed := check_function_for_property(property, cast(*Code_Procedure_Header, resolved), stack_of_functions);
		if !passed  return false;


	case .IDENT;
		// If the identifier resolves to a global, bad.
		// Else okay
		id := cast(*Code_Ident, it);
		decl_of_id := id.resolved_declaration;
		if !decl_of_id continue;
		if property & .DOES_NOT_ACCESS_GLOBALS 
		{
			if property & .GLOBAL_CONSTANTS_ARE_FINE && decl_of_id.flags & (.IS_CONSTANT | .IS_GLOBAL)
			{
				log("Is constant global");
			} else if decl_of_id.flags & .IS_GLOBAL
			{
				compiler_report(tprint("GLOBAL spotted %", it), make_location(it), .INFO);
				return false;
			}
		}


	case;
		//compiler_report(tprint("Unhandled Kind %", it.kind), make_location(it), .INFO);
	}
	pop(stack_of_functions);
	return true;
}


try_evaluate_to :: (node : *Code_Node, $T : Type) -> success : bool, value : T
{
	value : T;

	if node.type.type != .ENUM  
	{
		compiler_report("Type of the node is not an enum", make_location(node), .ERROR);
		return false, value;
	}


	t_enum := cast(*Type_Info_Enum, node.type);
	if t_enum.name != "Vibes" 
	{
		compiler_report("Name of Enum is not correct", make_location(node), .ERROR);
		return false, value;
	}

	if node.kind == 
	{
	case .BINARY_OPERATOR;
		binop := cast(*Code_Binary_Operator, node);
		left_succ, left_val := try_evaluate_to(binop.left, T);
		right_succ, right_val := try_evaluate_to(binop.right, T);

		if !left_succ || !right_succ  return false, value;

		if binop.operator_type ==
		{
		case #char "|";
			return true, left_val | right_val;
		}
	
	case .UNARY_OPERATOR;
		unop := cast(*Code_Unary_Operator, node);

		succ, val := try_evaluate_to(unop.subexpression, T);

		if !succ return false, val;
		if unop.operator_type ==
		{
		case #char ".";
			return true, val;
		case #char "~";
			return true, ~val;
		case;
			return false, val;
		}
	
	case .IDENT;
		ident := cast(*Code_Ident, node);
		#insert #run  -> string
		{
			b : String_Builder;
			builder := *b;
			for enum_names(Vibes)
			{
				print(builder, "if ident.name == \"%\"  return true, .%1;\n", it);
			}
			return builder_to_string(builder);
		};
		compiler_report(tprint("Failed to match % with any value in %", ident.name, Vibes), make_location(ident));
	case;
		compiler_report("Unsupported", make_location(node));
	}


	return false, value;
}
