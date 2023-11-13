#Prompt to GPT4 through bing: Write psuedocode for implementing the gsat algorithm 10/2/23 12:39pm

import os
import pandas as pd
import random
import copy
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
  
def prop_pure(expression):
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
        
    return expression, all_literals

#Given an expression, apply assignments and return the satisfied and unsatisfied clauses seperatly
def apply_assignments(expression, assignments):
    unsatisfied_clauses = []
    satisfied_clauses = []
    
    #Iterate through every clause
    for i in range(len(expression)):
        add_clause = 1
        for f in range(len(expression[i])):
            #If a positive literal in the clause is set to 1, the clause is satisfied and we can stop checking
            if(expression[i][f] > 0 and assignments[expression[i][f]] == 1):
                add_clause = 0
                break
            #If a negative literal in the clause is set to 0, the clause is satisfied and we can stop checking
            elif(expression[i][f] < 0 and assignments[expression[i][f] * -1] == 0):
                add_clause = 0
                break
                
        #Add the clause if it is unsatisfied
        if(add_clause):
            unsatisfied_clauses.append(expression[i])
        else:
            satisfied_clauses.append(expression[i])
    
    return unsatisfied_clauses, satisfied_clauses
 
def run_gsat(expression, attempts, flips):
    global min_unsatisfied_clauses
    min_unsatisfied_clauses = len(expression)

    #Before anything else, do unit propagation and pure literal elimination ... I also grab a list containing all literals
    expression, all_literals = prop_pure(expression)
    
    #Make negative values in all_literals positive if it does not already exists
    new_all_literals = []
    for i in range(len(all_literals)):
        if(all_literals[i] < 0):
            if(all_literals[i] * -1 not in all_literals):
                new_all_literals.append(all_literals[i] * -1)
        else:
            new_all_literals.append(all_literals[i])
    all_literals = new_all_literals
        
    #All literals will index a list of random assignments, indeces that don't have a literal will be -1 
    assignments = [-1] * (max(all_literals) + 1)
  
    #Try attemps # of times
    for i in range(attempts):
        #For an extra bit of help, I don't want to flip the same bit back and forth
        last_flipped_bit = 0
    
        #Assign each variable a value randomly
        for f in range(len(all_literals)):
            assignments[all_literals[f]] = random.randint(0,1)
        
        #For flips # of times
        for f in range(flips):
            #Get the satisfied and unsatisfied clauses given the current random assignment
            unsatisfied_clauses, satisfied_clauses = apply_assignments(expression, assignments)
            
            if(len(unsatisfied_clauses) < min_unsatisfied_clauses):
                min_unsatisfied_clauses = len(unsatisfied_clauses)
            
            #If the formula is satisfied return
            if(len(unsatisfied_clauses) == 0):
                print("SATISFIED WITH " + str(assignments))
                return 1
               
            #Otherwise get a list of all the variables from the unsatisfied_clauses
            unsatisfied_variables = []
            for c in range(len(unsatisfied_clauses)):
                for l in range(len(unsatisfied_clauses[c])):
                    if(abs(unsatisfied_clauses[c][l]) not in unsatisfied_variables):
                        unsatisfied_variables.append(abs(unsatisfied_clauses[c][l]))
            
            #For each variable in the unsatisfied_clauses
            diff_arr = []
            for v in range(len(unsatisfied_variables)):
                #Create a fake assignments list 
                test_assignments = copy.deepcopy(assignments)
            
                #Flip the variable for the test
                if(test_assignments[unsatisfied_variables[v]] == 0):
                    test_assignments[unsatisfied_variables[v]] = 1
                else:
                    test_assignments[unsatisfied_variables[v]] = 0
                    
                #Count how many unsatisfied clauses would become satisfied by flipping v
                unsat_test, sat_test = apply_assignments(unsatisfied_clauses, test_assignments)
                made_sat = len(unsatisfied_clauses) - len(unsat_test)
                
                #Count how many satisfied clauses would become unsatisfied by flipping v
                unsat_test, sat_test = apply_assignments(satisfied_clauses, test_assignments)
                made_unsat = len(satisfied_clauses) - len(sat_test)
                
                diff_arr.append(made_sat - made_unsat)

            #Make a list containing all the p values with the highest diff and the second highest diff
            highest_diff = max(diff_arr)
            
            flip_list = []
            flip_list.append(unsatisfied_variables[diff_arr.index(highest_diff)])

            #Pick a random value from flip_list
            rand_index = random.randint(0, len(flip_list) - 1)
            
            #Don't flip the same bit over and over
            if(last_flipped_bit == flip_list[rand_index]):
                #Instead flip a random variable that has a positive diff
                random_diff = -1
                timeout = 0
                while(random_diff < 0 and timeout < 10):
                    rand_diff_index = random.randint(0, len(diff_arr) - 1)
                    random_diff = diff_arr[rand_diff_index]
                    flip_list[0] = unsatisfied_variables[rand_diff_index] 
                    timeout = timeout + 1

            last_flipped_bit = flip_list[rand_index]
            
            #Flip it
            if(assignments[flip_list[rand_index]] == 0):
                assignments[flip_list[rand_index]] = 1
            else:
                assignments[flip_list[rand_index]] = 0
    
    print("NOT SATISFIED")
    return 0
    
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

tot = 0 #Delete later

for run in range(10):
    file_name = 'gsat_hard_cnf.csv'   #CHANGE THIS FOR EACH UNIQUE RUN
    
    file = open(file_name, 'a')
    file.write("STARTING ROUND " + str(run) + "\n")
    file.close()
    
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
            global min_unsatisfied_clauses 
            min_unsatisfied_clauses = total_clauses       
            
            #Run GSAT
            start_time = time.perf_counter()
            satisfied = run_gsat(expression,100,100)
            end_time = time.perf_counter()
            
            if(satisfied):
                tot = tot + 1
            
            print("\n--------------------\nTotal satisfied = " + str(tot))
            
            #Print the result
            print("Satisfiable: " + str(satisfied))
            print("CPU Time: " + str(end_time - start_time))
            print("Total clauses: " + str(total_clauses))
            print("Max satisfied: " +  str(total_clauses - min_unsatisfied_clauses))
            
            this_output = str(true_file_arr[i]) + "," + str(satisfied) + "," + str(end_time - start_time) + "," + str(total_clauses) + "," + str(total_clauses - min_unsatisfied_clauses)
        
            #Print the result to an excel file
            file_name = 'gsat_hard_cnf.csv'   #CHANGE THIS FOR EACH UNIQUE RUN
            
            file = open(file_name, 'a')
            file.write(this_output + "\n")
            file.close()