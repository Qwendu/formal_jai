

meter :: inline (value : $T) -> T
{
	return value;
}

second :: inline (value : $T) -> T
{
	return value;
}

unit_of :: ($c : Code, $loc := #caller_location) -> Unit
{
	compiler_query_metaprogram :: (identifier : string, any : Any) -> Any
	{
		// Maybe this sends a Message_Query with the above arguments?
		/*
Message_Query :: struct
{
	// ....
	query_identifier : string;
	payload          : Any;
}
		*/
		return UNIT_METER;
	}
	unit :: #run cast(*Unit, compiler_query_metaprogram(identifier = "Absolute_Unit.unit_of", c).value_pointer).*;
	return unit;
}

Fraction :: struct
{
	numerator   : s64;
	denominator : s64 = 1;
}

operator+ :: (l : Fraction, r : Fraction) -> Fraction
{
	shared_denom := l.denominator * r.denominator;
	f := Fraction.{
		numerator = l.numerator * r.denominator + r.numerator * l.denominator,
		denominator = shared_denom
	};
	return shorten_fraction(f);
}
operator- :: (l : Fraction, r : Fraction) -> Fraction
{
	shared_denom := l.denominator * r.denominator;
	f := Fraction.{
		numerator = l.numerator * r.denominator - r.numerator * l.denominator,
		denominator = shared_denom
	};
	return shorten_fraction(f);
}
operator* :: (l : Fraction, r : Fraction) -> Fraction
{
	f := Fraction.{
		numerator   = l.numerator * r.numerator,
		denominator = l.denominator * r.denominator
	};
	return shorten_fraction(f);
}
operator== :: (a : Fraction, b :Fraction) -> bool
{
	return a.numerator == b.numerator && a.denominator == b.denominator;
}

shorten_fraction :: (f : Fraction) -> Fraction
{
	#import "Math";
	shortened := f;
	i := 2;
	while cast(float64, i) < sqrt(cast(float64, shortened.denominator))
	{
		defer i += 1;
		while shortened.numerator % i == 0 && shortened.denominator % i == 0
		{
			shortened.numerator /= i;
			shortened.denominator /= i;
		}
	}
	return shortened;
}

FRACTION_ONE  :: Fraction.{1,1};
FRACTION_ZERO :: Fraction.{0,1};

Unit :: struct
{
	factor : Fraction;

	// These are now powers
	meter  : Fraction;
	second : Fraction;
};

UNIT_METER :: Unit.{
	FRACTION_ONE, 
	FRACTION_ONE,
	FRACTION_ZERO,
};

UNIT_SECOND :: Unit.{
	FRACTION_ONE, 
	FRACTION_ZERO,
	FRACTION_ONE,
};



#import "Compiler";
#import "Basic";
Unit_Checker :: struct
{
	#as using _ : Metaprogram_Plugin;
	message = messages;
	imports : [..] *Message_Import;
	converters : struct
	{
		meter  : [..] *Code_Procedure_Header;
		second : [..] *Code_Procedure_Header;
	};
};

get_plugin :: () -> *Metaprogram_Plugin
{
	p := New(Unit_Checker);
	return p;
}


messages :: (plug : *Metaprogram_Plugin, message : *Message)
{
	MODULE_PATH :: #run sprint("%module.jai", #filepath);
	checker := cast(*Unit_Checker, plug);
	if message.kind ==
	{
	case .IMPORT;
		imp := cast(*Message_Import, message);
		if(imp.module_type == .FILE)
		{
			if(imp.fully_pathed_filename == MODULE_PATH)
			{
				array_add(*checker.imports, imp);
			}
		}
	case .TYPECHECKED;
		tc := cast(*Message_Typechecked, message);
		get_converters_from_headers(checker, tc.procedure_headers);
		for tc.procedure_bodies
		{
			unit_check_body(checker, it.expression);
		}
	}
}

get_converters_from_headers :: (checker : *Unit_Checker, headers : [] Typechecked(Code_Procedure_Header))
{
	for headers
	{
		header := it.expression;
		if header.enclosing_load.enclosing_import == null  continue;
		if !array_find(checker.imports, header.enclosing_load.enclosing_import)  continue;
		if header.name == "meter"
		{
			array_add(*checker.converters.meter, header);
		}
		if header.name == "second"
		{
			array_add(*checker.converters.second, header);
		}
	}
}

unit_printer :: (builder : * String_Builder, any : Any, data : *void) -> bool
{
	if any.type == cast(*Type_Info)Unit
	{
		unit := cast(*Unit, any.value_pointer);
		print(builder, "%", unit.factor);
		if unit.meter.numerator != 0
		{
			print(builder, " meter");
			if unit.meter.numerator != 1  print(builder, "^(%)", unit.meter);
		}
		if unit.second.numerator != 0
		{
			print(builder, " second");
			if unit.second.numerator != 1  print(builder, "^(%)", unit.second);
		}
		return true;
	}
	if any.type == cast(*Type_Info)Fraction
	{
		frac := cast(*Fraction, any.value_pointer);
		if frac.numerator != 1
		{
			print(builder, "%/%", frac.numerator, frac.denominator);
		}else{
			print(builder, "%", frac.numerator);
		}
		return true;
	}
	return false;
}


#import "Hash_Table";
unit_check_body :: (checker : *Unit_Checker, body : *Code_Procedure_Body)
{
	c := context;
	c.print_style.struct_printer = unit_printer;
	push_context,defer_pop c;
	#import "Code_Visit";
	all_nodes : [..] *Code_Node;
	get_recursive_nodes_breadth_first(body.block, *all_nodes);


	found_unit_annotation := false;
	for all_nodes if it.kind == .PROCEDURE_CALL
	{
		called_proc := cast(*Code_Procedure_Header, cast(*Code_Procedure_Call, it).resolved_procedure_expression);
		found_unit_annotation ||= array_find(checker.converters.meter, called_proc);
		found_unit_annotation ||= array_find(checker.converters.second, called_proc);
		if found_unit_annotation  break;
	}

	if !found_unit_annotation  return;

	
	unit_mapping : Table(*Code_Node, Unit);
	
	work_list : [] *Code_Node = all_nodes;
	new_work_list := NewArray(all_nodes.count, *Code_Node);

	add_work :: (v : $T) #expand
	{
		assert(new_work_list.count < all_nodes.count);
		new_work_list.count += 1;
		new_work_list[new_work_list.count - 1] = v;
	}

	while true
	{
		new_work_list.count = 0;

		for work_list if it.kind == 
		{
		case .PROCEDURE_CALL;
			pc := cast(*Code_Procedure_Call, it);
			called_proc := cast(*Code_Procedure_Header, pc.resolved_procedure_expression);
			if array_find(checker.converters.meter, called_proc)
			{
				table_add(*unit_mapping, it, UNIT_METER);
				compiler_report("Meter", make_location(it), .INFO);
			}
			if array_find(checker.converters.second, called_proc)
			{
				table_add(*unit_mapping, it, UNIT_SECOND);
				compiler_report("Second", make_location(it), .INFO);
			}
		case .BINARY_OPERATOR;
			binop := cast(*Code_Binary_Operator, it);
			left_unit  := table_find_pointer(*unit_mapping, binop.left);
			right_unit := table_find_pointer(*unit_mapping, binop.right);
			if binop.operator_type == #char "."  continue;
			if left_unit && right_unit
			{
				succ, unit := merge_units(cast(Operator_Type, binop.operator_type), left_unit.*, right_unit.*);
				if !succ
				{
					compiler_report(tprint("Cannot perform Operation on units '% % %'", left_unit.*, operator_to_string(cast(Operator_Type, binop.operator_type)), right_unit.*), make_location(it));
					return;
				}
				table_add(*unit_mapping, it, unit);
			}else{
				add_work(it);
			}
		case .DECLARATION;
			decl := cast(*Code_Declaration, it);
			if decl.expression
			{
				unit_of_decl_expression := table_find_pointer(*unit_mapping, decl.expression);
				if unit_of_decl_expression
				{
					table_add(*unit_mapping, decl, unit_of_decl_expression.*);
				}else{
					add_work(decl);
				}
			}else{
				table_add(*unit_mapping, decl, .{});
			}
		case .IDENT;
			id := cast(*Code_Ident, it);
			if id.type.type == 
			{
			case .PROCEDURE;       continue;
			case .POINTER;         continue;
			case .OVERLOAD_SET;    continue;
			case .TYPE;            continue;
			case .CODE;            continue;
			case .UNTYPED_LITERAL; continue;
			case .UNTYPED_ENUM;    continue;
			case .VARIANT;         continue;
			}
			unit_of_decl := table_find_pointer(*unit_mapping, id.resolved_declaration);
			if unit_of_decl  table_add(*unit_mapping, id, unit_of_decl.*);
			else             add_work(id);
		case .BLOCK;
		case .LITERAL;
		case;
			add_work(it);
		}

		if work_list.count == new_work_list.count 
		{
			for new_work_list
			{
				//compiler_report(tprint("Failed to resolve %", it.kind), make_location(it), .INFO);
			}
			//compiler_report("Failing to make progress", make_location(body));
			break;
		}
		work_list, new_work_list = new_work_list, work_list;
	}
	
	for unit_mapping
	{
		//compiler_report(tprint("Unit %", it), make_location(it_index), .INFO);
	}

}

units_are_equal :: (a : Unit, b : Unit) -> bool
{
	return a.factor == b.factor && a.meter == b.meter && a.second == b.second;
}

merge_units :: (op : Operator_Type, left : Unit, right : Unit) -> succes : bool, Unit
{
	if op ==
	{
	case #char "-"; #through;
	case #char "+";
		return units_are_equal(left, right), left;
	case #char "*";
		return true, .{
			factor = left.factor * right.factor,
			meter  = left.meter  + right.meter,
			second = left.second + right.second
		};
	case #char "/";
		return true, .{
			factor = left.factor * Fraction.{right.factor.denominator, right.factor.numerator},
			meter  = left.meter  - right.meter,
			second = left.second - right.second
		};
	}
	return true, .{};
}


