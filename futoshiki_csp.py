
'''
All models need to return a CSP object, and a list of lists of Variable objects 
representing the board. The returned list of lists is used to access the 
solution. 

For example, after these three lines of code 

    csp, var_array = futoshiki_csp_model_1(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the Futoshiki puzzle.

1. futoshiki_csp_model_1 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only 
      binary not-equal constraints for both the row and column constraints.

2. futoshiki_csp_model_2 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only n-ary 
      all-different constraints for both the row and column constraints. 

'''
from cspbase import *
import itertools

def futoshiki_csp_model_1(futo_grid):    
    n = len(futo_grid)
    num_col = len(futo_grid[0])
    csp = CSP("Futoshiki CSCP Model 1 - {}x{}".format(n, n))
    
    variables = []
    var_domain = []
    
    for i in range(0, n):
        var_domain.append(i + 1);
        variables.append([])
        
    for row in range(n):
        for col in range(num_col):
            if col % 2 == 0: # this is a var
                var = var_setup(futo_grid = futo_grid, var_domain = var_domain, row = row, col = col)
                variables[row].append(var)
                csp.add_var(var)
            elif (col > 0 and (futo_grid[row][col - 1] == '<' or futo_grid[row][col - 1] == '>')):
                # add constraint btwn the curr var and the previous var
                ineq_constraint(csp = csp, futo_grid = futo_grid, variables = variables, var1 = variables[row][int(col/2) - 1], var2 = variables[row][int(col/2)], greater_than = (futo_grid[row][col - 1] == '>'), row = row, col = col)
    
    # # create row constraints
    for i in range(n): #each row
        for j in range(n):
            for k in range(j+1, n):
                binary_constraint(csp = csp, variables = variables, row_constraint = True, row = i, col1 = j, col2 = k, col = i, row1 = j, row2 = k)
                binary_constraint(csp = csp, variables = variables, row_constraint = False, row = i, col1 = j, col2 = k, col = i, row1 = j, row2 = k)
                                
    return (csp, variables)
    
def futoshiki_csp_model_2(futo_grid):
    n = len(futo_grid)
    num_col = len(futo_grid[0])
    csp = CSP("Futoshiki CSCP Model 2 - {}x{}".format(n, n))
    
    variables = []
    var_domain = []
    row_domains = []
    
    for i in range(0, n):
        var_domain.append(i + 1);
        variables.append([])
        row_domains.append([])
    
    for row in range(n):
        for col in range(num_col):
            if col % 2 == 0: # this is a var
                var = var_setup(futo_grid = futo_grid, var_domain = var_domain, row = row, col = col)
                variables[row].append(var)
                row_domains[row].append(var.cur_domain())
                csp.add_var(var)
            elif (col > 0 and (futo_grid[row][col - 1] == '<' or futo_grid[row][col - 1] == '>')):
                # add constraint btwn the curr var and the previous var
                ineq_constraint(csp=csp, futo_grid = futo_grid, variables = variables, var1 = variables[row][int(col/2) - 1], var2 = variables[row][int(col/2)], greater_than = (futo_grid[row][col - 1] == '>'), row = row, col = col)
                
    for i in range(n):
        col_vars = []
        col_domains = []
        
        for j in range(n):
            col_vars.append(variables[j][i])
            col_domains.append(variables[j][i].cur_domain())
        
        all_diff_constraint(csp=csp, vars=variables[i], domains=row_domains[i], num_vars=n)
        all_diff_constraint(csp=csp, vars=col_vars, domains=col_domains, num_vars=n)
        
    return (csp, variables)

def all_diff_constraint(csp, vars, domains, num_vars):
    con = Constraint("{})".format(":("), vars)
    sat_tuples = []
    every_tuple = [[]]
    
    for pool in domains:
        every_tuple = [x+[y] for x in every_tuple for y in pool]
    
    for possible_tuple in every_tuple:
        valid = True
        for i in range(num_vars):
            for j in range(i+1, num_vars):
                if possible_tuple[i] == possible_tuple[j]:
                    valid = False
        if valid:
            sat_tuples.append(possible_tuple)

    con.add_satisfying_tuples(sat_tuples)
    csp.add_constraint(con)
    
def var_setup(futo_grid, var_domain, row, col):
    var_name = "V{}{}".format(row, int(col/2))
    
    if(futo_grid[row][col] == 0): # if var is unassigned
        var = Variable(var_name, var_domain)
    else: # if var is assigned
        var = Variable(var_name, [futo_grid[row][col]])

    return var

def ineq_constraint(csp, futo_grid, variables, var1, var2, greater_than, row, col):   
    con = Constraint("C {}{}{}{}{}".format(row,int(col/2)-1,futo_grid[row][col-1],row,int(col/2)),[var1, var2])
    sat_tuples = []
    
    for val1 in var1.cur_domain():
        for val2 in var2.cur_domain():
            if ((greater_than and val1 > val2) or (not greater_than and val1 < val2)):
                sat_tuples.append((val1, val2))
    con.add_satisfying_tuples(sat_tuples)
    csp.add_constraint(con)

def binary_constraint(csp, variables, row_constraint, row, col1, col2, col, row1, row2):
    if row_constraint:
        var1 = variables[row][col1]
        var2 = variables[row][col2]
        con = Constraint("C {}{}!={}{}".format(row,col1,row,col2), [var1, var2])
    else:
        var1 = variables[row1][col]
        var2 = variables[row2][col] 
        con = Constraint("C {}{}!={}{}".format(row1,col,row2, col), [var1, var2])
        
    sat_tuples = []
    for val1 in var1.cur_domain():
        for val2 in var2.cur_domain():
            if (val1 != val2):
                sat_tuples.append((val1, val2))
                
    con.add_satisfying_tuples(sat_tuples)
    csp.add_constraint(con)