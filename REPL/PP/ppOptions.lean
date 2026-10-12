import Lean

open Lean

def ppOptions (options : Options) : Options :=
  options
    |>.setBool `pp.notation false
    |>.setBool `pp.unicode false
    |>.setBool `pp.unicode.fun false
    |>.setBool `pp.match false
    |>.setBool `pp.coercions false
    |>.setBool `pp.coercions.types true
    |>.setBool `pp.fullNames true
    |>.setBool `pp.funBinderTypes true
    |>.setBool `pp.piBinderTypes true
    |>.setBool `pp.piBinderNames true
    |>.setBool `pp.foralls true
    |>.setBool `pp.letVarTypes true
    |>.setBool `pp.numericTypes true
    |>.setBool `pp.mvars.withType true
    |>.setBool `pp.structureInstances false
    |>.setBool `pp.safeShadowing false
