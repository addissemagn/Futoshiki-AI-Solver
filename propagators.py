'''This file will contain different constraint propagators to be used within 
   bt_search. 

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
		 
		 
var_ordering == a function with the following template
    var_ordering(csp)
        ==> returns Variable 

    csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.
   '''

import math

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0: # of unassigned vars in constraints scope 
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
        
    pruned = []
    
    for c in csp.get_all_cons() if not newVar else csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 1: # only one unassigned variable
            for var in c.get_scope(): # vars in the scope of the constraint
                if not var.is_assigned(): # find the one that is not assigned             
                    
                    for value in var.cur_domain(): #  check that every var in the domain of unassigned_var has support
                        if not c.has_support(var, value): 
                            var.prune_value(value)
                            pruned.append((var, value))
            
                    if len(var.cur_domain()) == 0:
                        return False, pruned
    
    return True, pruned

def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    #IMPLEMENT
    
    pruned = []
    constraint_queue = csp.get_all_cons() if not newVar else csp.get_cons_with_var(newVar)
    
    for constraint in constraint_queue:
        for var in constraint.get_unasgn_vars(): # get unassigned vars in constraint
            pruned_from = False
    
            # now check that every var in the domain of unassigned_var has support
            for val in var.cur_domain():
                if not constraint.has_support(var, val):
                    var.prune_value(val)
                    pruned.append((var, val))
                    pruned_from = True
    
            if len(var.cur_domain()) == 0: # domain wipe out
                return False, pruned
            
            if pruned_from:
                for cons in csp.get_cons_with_var(var):
                    constraint_queue.append(cons)
                    
    return True, pruned

def ord_mrv(csp):
    ''' return variable according to the Minimum Remaining Values heuristic '''
    #IMPLEMENT
    
    dom_count = math.inf 
    mrv = csp.get_all_vars().pop(0)
    
    for var in csp.get_all_vars():
        count = 0
        for val in var.cur_domain():
            count += 1
            
        if count < dom_count:
            dom_count = count
            mrv = var
    
    return mrv