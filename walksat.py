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
 
def run_walksat(expression, random_probability, flips):

# function WALKSAT(clauses, p, max_flips) returns a satisfying model or failure
#  inputs: clauses, a set of clauses in propositional logic
#     p, the probability of choosing to do a "random walk" move, typically around 0.5
#     max_flips, number of flips allowed before giving up

#  model ← a random assignment of true/false to the symbols in clauses
#  for i = 1 to max_flips do
#    if model satisfies clauses then return model
#    clause ← a randomly selected clause from clauses that is false in model
#    with probability p flip the value in model of a randomly selected symbol from clause
#    else flip whichever symbol in clause maximizes the number of satisfied clauses
# return failure

    #Track the minimum number of unsatisfied clauses to determine max satisfied clauses
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
    
    #Assign each variable a value randomly
    for f in range(len(all_literals)):
        assignments[all_literals[f]] = random.randint(0,1)
  
    #Try flips # of times
    for i in range(flips):
    
        #Get the satisfied and unsatisfied clauses given the current random assignment
        unsatisfied_clauses, satisfied_clauses = apply_assignments(expression, assignments)
        
        #print("The number of satisfied_clauses is " + str(len(satisfied_clauses)))
        
        #Update the min unsatisfied clauses
        if(len(unsatisfied_clauses) < min_unsatisfied_clauses):
            min_unsatisfied_clauses = len(unsatisfied_clauses)
        
        #If the formula is satisfied return
        if(len(unsatisfied_clauses) == 0):
            print("SATISFIED WITH " + str(assignments))
            return 1
                
        #Randomly select an unsatisfied clause
        random_clause = unsatisfied_clauses[random.randint(0,len(unsatisfied_clauses) - 1)]
        
        #print("The random clause is " + str(random_clause))
        
        #Generate a random number 1-100 
        random_decision = random.randint(1,100)
        
        #If the random number is less than random_probability, flip the value of a random literal in clause
        if(random_decision < random_probability):
            #Choose a random literal (And make it positive to index our assignments array)
            random_literal = abs(random_clause[random.randint(0,len(random_clause) - 1)])
            
            #And flip it
            #print("I'm flipping a random literal : " + str(random_literal))
            if(assignments[random_literal] == 0):
                assignments[random_literal] = 1
            else:
                assignments[random_literal] = 0
        #Otherwise, flip the literal that maximizes the number of satisfied_clauses (from random_clause)
        else:
            best_literal = 0
            max_satisfied = 0
            #Iterate through every literal in the clause
            for literal in range(len(random_clause)):
                #Create a fake assignments list 
                test_assignments = copy.deepcopy(assignments)
                
                #Flip the variable for the test
                if(test_assignments[abs(random_clause[literal])] == 0):
                   test_assignments[abs(random_clause[literal])] = 1
                else:
                    test_assignments[abs(random_clause[literal])] = 0
                    
                #Count how many satisfied clauses get returned
                unsat_test, sat_test = apply_assignments(expression, test_assignments)
                
                #If the clauses satisfied is greater than the current maximum, we save this as our best literal
                if(len(sat_test) > max_satisfied):
                    max_satisfied = len(sat_test)
                    best_literal = abs(random_clause[literal])
            
            #When the loop ends we flip the best literal (because it had the most satisfied clauses
            #print("I'm flipping the best literal : " + str(best_literal))
            if(assignments[best_literal] == 0):
                assignments[best_literal] = 1
            else:
                assignments[best_literal] = 0            
        
    #If we timeout we fail
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
    file_name = 'walksat_hard_cnf.csv'   #CHANGE THIS FOR EACH UNIQUE RUN
    
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
            satisfied = run_walksat(expression,50,1000)
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
            file_name = 'walksat_hard_cnf.csv'   #CHANGE THIS FOR EACH UNIQUE RUN
            
            file = open(file_name, 'a')
            file.write(this_output + "\n")
            file.close()