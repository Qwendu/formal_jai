Units :: #import "AbsoluteUnit";
#import "Basic";


main :: ()
{
distance := Units.meter(3.);
time     := Units.second(2.3);
velocity :=  distance/time;
print("%\n", Units.unit_of(velocity)); // Currently not possible to implement
//Units.check_unit(unit_of(velocity) == meter) // somehow be able to assert units.
}
