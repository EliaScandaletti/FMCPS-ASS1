import pynusmv
import sys

def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def check_explain_inv_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ending with a state. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    
    function SymbolicReachable(Init, Trans, Inv)
        Reach ← Init
        New ← Init
        while not IsEmpty(New) do
            if not IsEmpty(Intersect(New, Not(Inv))) then
                return False
            end if
            New ← Diff(Post(New,Trans), Reach)
            Reach ← Union(Reach, New)
        end while
        return True
    end function
    """


    # a + b and a | b compute the disjunction of a and b
    # a * b and a & b compute the conjunction of a and b
    # ~a and -a compute the negation of a
    # a - b computes a & ~b
    # a ^ b computes the exclusive-OR (XOR) of a and b
    # a == b, a <= b, a < b, a > b and a >= b compare a and b


    model = pynusmv.glob.prop_database().master.bddFsm
    invariant = spec_to_bdd(model, spec)
    not_invarinat = ~invariant

    reach = model.init
    new = model.init
    trace = []

    while not new.is_false():
        if new.intersected(not_invarinat):
            # trace = ...
            return False, trace
        new = model.post(new) - reach
        reach = reach + new
    return True, None


    # for state in model.pick_all_states(invariant):
    #     print(state.get_str_values())


if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")
        res, trace = check_explain_inv_spec(spec)
        if res == True:
            print("Invariant is respected")
        else:
            print("Invariant is not respected")
            print(trace)
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()
