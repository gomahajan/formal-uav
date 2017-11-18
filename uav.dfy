method run() returns (done: int)
{
  // Definitions
  var sensor_x := 1;
  var charging_x := 0;
  
 // Variables in system
  var drone_x := 0;
  var battery := 100;
  var queue := 0;
  
 var battery_cost := 20; // Battery cost to go from 0 to 1 and other way around
  
 var t := 0;
  while t < 100
    invariant 0<=t<=100;
    invariant battery - queue > 0;
    decreases 101-t;
  {
  // Decision
  var choice := 0;
  
 if battery > 20
  {
    choice := 1;
  }
  
 if choice == 0
    {
      drone_x := 0;
      battery := 100;
      queue := queue + 10;      
    }
  else
    {
      drone_x := 1;
      battery := battery-battery_cost;
      queue := 0;
    }
    t := t + 1;
  }
  
 return 1;
}
