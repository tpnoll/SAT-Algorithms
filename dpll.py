import os
import pandas as pd
import time

# Zeros represent no literal, I can clean up my data structure by removing them
def remove_all_zeros(expression):
    #Create a new expression we can return
    new_expression = []
    
    #Iterate through every clause
    for i in range(len(expression)):
        #Create a new clause that will have zeros removed
        new_clause = []
        
        #Iterate through every  literal
        for f in range(len(expression[i])):
            #If the literal is not zero we append it to the new clause
            if(expression[i][f] != 0):
                new_clause.append(expression[i][f])
    
        #Add the new clause to the new expression
        new_expression.append(new_clause)
    
    #Return the new expression
    return new_expression

#Given an expression and the literal from a unit clause, perform unit propagation
def unit_propagation(expression, literal):
    #Calculate the compliment of the literal
    compliment = literal * -1

    #Create a new expression we can return
    new_expression = []
    
    #Iterate through every clause
    for i in range(len(expression)):
        #Create a new clause
        new_clause = []
        
        #Boolean to track if a clause contains a literal
        contains_literal = 0
        
        #Iterate through every  literal
        for f in range(len(expression[i])):
            #If the literal exists in this clause
            if(expression[i][f] == literal):
                #Mark the boolean to remove this clause
                contains_literal = 1
                break
            #Otherwise add literals that don't match the compliment
            elif(expression[i][f] != compliment):
                new_clause.append(expression[i][f])
    
        #Add the new clause to the new expression if literal was not found
        if(contains_literal == 0):
            new_expression.append(new_clause)
    
    #Return the new expression
    return new_expression
  
def run_dpll(expression):
    global total_iterations
    total_iterations = total_iterations + 1
    
    #First do all possible unit propagation
    do_unit_prop = 1
    while(do_unit_prop):
        do_unit_prop = 0
        #As long as there is still a unit clause, unit propagation must continue
        for i in range(len(expression)):
            if(len(expression[i]) == 1):
                #This expression contains a single literal
                do_unit_prop = 1
                expression = unit_propagation(expression, expression[i][0])
                break
                
    #Next eliminate all pure literals
    do_pure_lit = 1
    while(do_pure_lit):
        #Make a list of every literal in the expression
        all_literals = []
        for i in range(len(expression)):
            for f in range(len(expression[i])):
                if(expression[i][f] not in all_literals):
                    all_literals.append(expression[i][f])
                    
        #Then make a list that only contains the pure literals
        pure_literals = []
        for i in range(len(all_literals)):
            if((all_literals[i] * -1) not in all_literals):
                pure_literals.append(all_literals[i])
                
        #If pure_literals is empty we can leave the loop
        if(len(pure_literals) == 0):
            do_pure_lit = 0
                
        #Go through and remove all clauses that contain a pure literal
        new_expression = []
        for i in range(len(expression)):
            found_pure_literal = 0
            for f in range(len(pure_literals)):
                if(pure_literals[f] in expression[i]):
                    found_pure_literal = 1
                    break
            if(found_pure_literal == 0):
                new_expression.append(expression[i])
        expression = new_expression

    #The number of clauses in expression at this point is the current number of unsatisfied clauses
    global unsatisfied_clauses
    if(len(expression) < unsatisfied_clauses):
        unsatisfied_clauses = len(expression)
    
    #If the expression is empty, return true
    if(len(expression) == 0):
        return 1, expression
        
    #If the expression contains an empty clause, return false
    for i in range(len(expression)):
        if(len(expression[i]) == 0):
            return 0, expression
            
    #If we continue, choose a literal (for now I'll choose the first one in all_literals)
    norm_literal = all_literals[0]
    anti_literal = norm_literal * -1
    
    #Set norm_literal to 1 and anti_literal to 0 and save in norm_expression
    norm_expression = []
    for i in range(len(expression)):
        new_clause = []
        add_clause = 1
        for f in range(len(expression[i])):
            if(expression[i][f] == norm_literal):
                add_clause = 0
                break
            elif(expression[i][f] != anti_literal):
                new_clause.append(expression[i][f])
        if(add_clause):
            norm_expression.append(new_clause)
            
    #Run dpll on norm_expression
    norm_result, norm_expression = run_dpll(norm_expression)
    
    #If its true, return
    if(norm_result):
        return norm_result, norm_expression
   
    #Otherwise calculate the anti_expression and return that
    anti_expression = []
    for i in range(len(expression)):
        new_clause = []
        add_clause = 1
        for f in range(len(expression[i])):
            if(expression[i][f] == anti_literal):
                add_clause = 0
                break
            elif(expression[i][f] != norm_literal):
                new_clause.append(expression[i][f])
        if(add_clause):
            anti_expression.append(new_clause)        
            
    anti_result, anti_expression = run_dpll(anti_expression)
    return anti_result, anti_expression
 
#Specify a folder that contains multiple files to check
def check_folder(path):
    #Files contain all of the files, but also the .. and . directories 
    true_file_arr = []
    for files in os.walk(path):
        #Save only the files we want to open to the true_file_arr
        for file_arr in files:
            if(len(file_arr) > 0 and file_arr[0].endswith('.cnf')):
                true_file_arr = file_arr
                break              
    
    return true_file_arr
    
def pre_process_file(file):
    expression = []

    #Pre-process the file
    for line in file:
        #If we reach the % we stop
        if(line[0] == '%'):
            break
        #Skip the beginning lines that start with c or p
        new_clause = []
        if((line[0] != 'c') & (line[0] != 'p')):
            #Then deliminate the line by spaces
            line_arr = line.split(' ')
            
            #Convert everything to int that can be
            for i in range(len(line_arr)):
                try:
                    new_clause.append(int(line_arr[i]))
                except:
                    pass
        
        if(len(new_clause) > 0):
            expression.append(new_clause)
        
    #Close the file
    file.close()
    
    return expression
    
#Specifiy the folder we want to check: Make sure the path has a final / on the end
path = 'PA3_Benchmarks/PA3_Benchmarks/HARD CNF Formulas/'  

#Get an array of all the files in that folder
true_file_arr = check_folder(path)

output_arr = []

#Now iterate through the true file array
for i in range(len(true_file_arr)):
    print("\nChecking file: " + true_file_arr[i])
    
    if(true_file_arr[i].endswith('.cnf')):
        #Open the file
        file = open(path + true_file_arr[i], 'r') 

        #Preprocess the file
        expression = pre_process_file(file)        
        
        #Remove all zeros from the clause
        expression = remove_all_zeros(expression)        
        
        #Use a global variable to track the maximum number of satisfied clauses
        total_clauses = len(expression)
        global unsatisfied_clauses
        unsatisfied_clauses = total_clauses
        global total_iterations
        total_iterations = 0
        
        #Run DPLL
        start_time = time.perf_counter()
        result, expression = run_dpll(expression)
        end_time = time.perf_counter()        
        
        #Print the result
        print("Satisfiable: " + str(result))
        print("CPU Time: " + str(end_time - start_time))
        print("Total clauses: " + str(total_clauses))
        print("Max satisfied: " +  str(total_clauses - unsatisfied_clauses))
        
        
        this_output = str(true_file_arr[i]) + "," + str(result) + "," + str(end_time - start_time) + "," + str(total_clauses) + "," + str(total_clauses - unsatisfied_clauses)

        #Print the result to an excel file
        file_name = 'timed_dpll_hard_cnf.csv'   #CHANGE THIS FOR EACH UNIQUE RUN

        file = open(file_name, 'a')
        file.write(this_output + "\n")
        file.close()
    
