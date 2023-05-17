/* Toy car state machine.  */

datatype Gear = Park | Reverse | Drive
datatype Variables = Variables(
  garageOpen: bool,
  carRunning: bool,
  gear: Gear,
  carInDriveway: bool
)

ghost predicate Init(v: Variables)
{
  && !v.garageOpen
  && !v.carRunning
  && v.gear == Park
  && !v.carInDriveway
}

datatype Step =
  | OpenGarageStep
  | StartCarStep
  | PutCarInGearStep
  | ReverseCarStep

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step
  // We can kick things off at any time by opening the garage.
  case OpenGarageStep =>
    !v.garageOpen && v' == v.(garageOpen := true)

  // Each subsequent step requires the previous step to run.
  case StartCarStep =>
    v.garageOpen && v' == v.(carRunning := true)
  case PutCarInGearStep =>
    v.carRunning && v' == v.(gear := Reverse)
  case ReverseCarStep =>
    v.gear == Reverse && v' == v.(carInDriveway := true)
}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

ghost predicate Safety(v: Variables)
{
  // Safety says that if the car is in the driveway, we have opened the garage.
  // This is true because we opened it way back at the beginning and kept it
  // open afterward.
  && v.carInDriveway ==> v.garageOpen
}

ghost predicate Inv(v: Variables)
{
  && Safety(v)
  && (v.gear == Reverse ==> v.garageOpen)
  && (v.carRunning ==> v.garageOpen)
}

lemma InitImpliesInv(v: Variables)
  requires Init(v)
  ensures Inv(v)
{}

lemma InvImpliesSafety(v: Variables)
  requires Inv(v)
  ensures Safety(v)
{}

lemma InvInductive(v: Variables, v': Variables)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{
  // Try removing the extra conjuncts from the invariant and notice what happens
  // in this debugging process. For example, Safety alone is not inductive
  // because it allows !v.garageOpen && v.gear == Reverse, but afterward
  // v'.carInDriveway will be true and the garage is not open. This state v is
  // unreachable, as proven by the additional invariants.
  var step :| NextStep(v, v', step);
  match step {
    case OpenGarageStep => {
      assert Inv(v');
    }
    case StartCarStep => {
      assert Inv(v');
    }
    case PutCarInGearStep => {
      assert Inv(v');
    }
    case ReverseCarStep => {
      assert Inv(v');
    }
  }
}

// Here's an alternate invariant that connects each step to the previous one.

ghost predicate InvAdjacentSteps(v: Variables)
{
  && Safety(v)
  && (v.carInDriveway ==> v.gear == Reverse)
  && (v.gear == Reverse ==> v.carRunning)
  && (v.carRunning ==> v.garageOpen)
}

lemma InvAdjacentInductive(v: Variables, v': Variables)
  requires InvAdjacentSteps(v)
  requires Next(v, v')
  ensures InvAdjacentSteps(v')
{
}

lemma InvAdjacentStricter()
  ensures forall v :: InvAdjacentSteps(v) ==> Inv(v)
  ensures !(forall v :: Inv(v) ==> InvAdjacentSteps(v))
{
  // Witness that shows Inv(v) can be true but InvAdjacentSteps is not
  //
  // If the protocol could turn the car off or get the car out of Reverse, then
  // Inv would still be an invariant but InvAdjacentSteps would no longer work.
  var v := Variables(
    garageOpen := true,
    carRunning := false,
    gear := Drive,
    carInDriveway := true
  );
  assert Inv(v) && !InvAdjacentSteps(v);
}
