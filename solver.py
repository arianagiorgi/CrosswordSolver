#! /usr/bin/python

## @package solver.py
# Solves a puzzle using components to generate candidates
#
# Steve Wilson
# Edited: Rui Zhang
# Apr 2014
# July 2014

import sys
import re
import argparse
import string
import subprocess
import random
import time
import csp.csp as csp
import puzzle
import copy
from component_thread import myThread

# @param puz the puzzle object
# @param candidates_file input file of candidate answers
# @param limit only take the top <limit> answers
def generate_all_candidates(puz,limit,score_adjust,candidates_output=None):
    print
    print "======================== Merge All candidats answers ================"
    data = []
    if candidates_output:
        data = candidates_output.split('\n')
    else:
        data = sys.stdin()
    answers_given = {}
    for line in data:
        print "line", line
        if line == "":
            continue
        clue_id = None
        answer = None
        component_source = None
        score = 1
        try:
            items = line.split('\t')
            assert len(items) in [2,3,4]
        except:
#            raise IOError("format not recognized for line: "+line)
            continue
        else:
            if len(items) >= 2:
                clue_id,answer = items[:2]
            if len(items) >= 3:
                score = float(items[2])
            if len(items) == 4:
                component_source = items[3]
                score += score_adjust
            else:
                print "==========================abnormal length====================="

        # make sure answer given is correct length
        assert len(answer) == puz.entries[clue_id].length

        if clue_id not in answers_given:
            answers_given[clue_id] = []
        skip = False
        for i in range(len(answers_given[clue_id])):
            if answer.upper() == answers_given[clue_id][i][0]:
                answers_given[clue_id][i]=(answer.upper(),float(score)+answers_given[clue_id][i][1],answers_given[clue_id][i][2]+[component_source])
                skip=True
        if not skip:
            answers_given[clue_id].append((answer.upper(),float(score),[component_source]))


    candidates = {}
    unanswered_clues = []
    for k in puz.entries.keys():
        if k in answers_given:
            candidates[k] = [x[0] for x in sorted(answers_given[k],key=lambda x:x[1], reverse=True)[:limit]]
        else:
            #give unanswered_clue candidates as "-----"
            unanswered_clues.append(k)
            candidates[k] = []
            candidates[k].append('-'*puz.entries[k].length)

    puz.all_candidates = answers_given
    weights_dict = {}

    for k,answers in answers_given.items():
        weights_dict[k] = {}
        for answer in answers:
            weights_dict[k][answer[0]]=answer[1]


    #return candidates,weights_dict,unanswered_clues
    ''' evaluate merger results "candidates" '''
    rank_of_candidates = {}
    cnt = 0
    rank_sum = 0
    for k in candidates.keys():
        if candidates[k][0] != '-':
            correct_answer = puz.entries[k].answer
            rank = 0
            find = False

            for candidate in candidates[k]:
                rank = rank + 1
                if candidate == correct_answer.upper():
                    rank_of_candidates[k] = rank
                    find = True
                    cnt = cnt + 1
                    rank_sum = rank_sum + rank
                    break

            if find == False:
                rank_of_candidates[k] = -1
        else:
            rank_of_candidates[k] = -1
    if cnt == 0:
        cnt = 1

    cnt_2 = 0
    temp_S = {}
    rank_answers = {}
    for k in puz.entries.keys():
        temp_S[k] = '-'*puz.entries[k].length
        rank_answers[k] = -1

    for k in answers_given.keys():
        rank = 0
        correct_answer = puz.entries[k].answer
        for candidate_tuple in sorted(answers_given[k],key=lambda x:x[1],reverse=True):
            rank += 1
            if correct_answer.upper() == candidate_tuple[0]:
                temp_S[k] = correct_answer
                rank_answers[k] = rank
                cnt_2 = cnt_2 + 1
                break

    ''' print how many candidates answers are generated for each clue'''
    tup_list = []
    for k in sorted(puz.entries.keys()):
        if k in answers_given.keys():
            if len(candidates[k])>1:
                first_score = weights_dict[k][candidates[k][0]]
                second_score = weights_dict[k][candidates[k][1]]
            else:
                first_score = weights_dict[k][candidates[k][0]]
                second_score = 0
            tup_list.append((k,rank_answers[k],len(answers_given[k]),first_score,first_score-second_score))

        else:
            tup_list.append((k,rank_answers[k],0,0,0))
    for tup in sorted(tup_list,key=lambda x:x[3],reverse=True):
        #print tup[0]+'\t'+str(tup[1])+' \ '+ str(tup[2])+'\t\t'+str(tup[3])+'\t'+str(tup[4])
        print tup[0]+'\t'+str(tup[1])+' \ '+ str(tup[2])

    print "max"+"\t"+str(max([rank_answers[k] for k in rank_answers.keys()]))+'/'+str(max([len(answers_given[k]) for k in answers_given.keys()]))

    cnt_3 = 0
    for k in temp_S.keys():
        temp_S = puz.update_solution(temp_S,k)
    for k in temp_S.keys():
        if temp_S[k].upper() == puz.entries[k].answer.upper():
            cnt_3 += 1



    print
    print "number of clues: " , len(puz.entries.keys())
    print "number of clues answered by some component: " , len(answers_given.keys())
    print "number of clues answered correctly by some component: " , cnt_2, "(",cnt_3,")"
    print "number of clues answered correctly in candidates list of CSP: " , cnt
    print "with average rank: " , float(rank_sum)/cnt  , "/" , limit
    print

    return candidates,weights_dict,unanswered_clues


class RebusError(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)

def propagate(next_var, next_val, puz, domains, neighbors, S):
    #print 'calling propagate ...........'

    # Check for assigned neighbors of next variable
    for neighbor in neighbors[next_var]:
        # if this neighbor is already assigned
        if neighbor in S.keys():
            if puz.check_intersect(neighbor,S[neighbor],next_var,next_val) == False:
                return False, None, None

    # Give assignment to next variable
    next_S = copy.deepcopy(S)
    next_S[next_var] = next_val
    next_S = puz.update_solution(next_S,next_var)

    # Pop next variable in next_domains
    next_domains = copy.deepcopy(domains)
    next_domains.pop(next_var)

    # Check for non-assigned neighbors of next variable
    for neighbor in neighbors[next_var]:
        if neighbor not in S.keys():
            for neighbor_candidate in domains[neighbor]:
                # if conflict, remove it
                if puz.check_intersect(neighbor,neighbor_candidate,next_var,next_val) == False:
                    next_domains[neighbor].remove(neighbor_candidate)

    return True, next_domains, next_S


# A crude search algorithm
# def solve_recursive(puz,variables,domains,neighbors,S):
#     # print 'calling solve_recursive.....'

#     # If all variables assgined, update solution
#     if len(variables) == len(S.keys()):
#         print "CSP complete"
#         return S

#     unassigned_vars = list( set(variables) - set(S.keys()) )
#     next_var = unassigned_vars[0]

#     if (len(domains[next_var])==0):
#         S[next_var] = '-'*puz.entries[next_var].length
#         for k in S.keys():
#             S = puz.update_solution(S,k)
#         return solve_recursive(puz,variables,domains,neighbors,S)
#     else:
#         next_val = domains[next_var][0]
#         success, next_domains, next_S = propagate(next_var,next_val,puz,domains,neighbors,S)
#         return solve_recursive(puz,variables,next_domains,neighbors,next_S)

# Edited search algorithm

#initialize n
n = 100

def solve(puz,domains,neighbors,S,B,n,P,variables,weight_dict):

    #If S assigns every variable, return whichever of S or B has the higher score
    if len(variables) == len(S.keys()):
        #print "CSP complete"
        #scores are equal to sum of the scores of all the words
        scoreS = 0
        for k in S:
	    if "-" not in S[k]: #if the word doesn't have "-"
		if S[k] in weight_dict[k]: #and it's a valid word
                    wordweight = weight_dict[k][S[k]]
		else:
		    wordweight = 0
	    else:
		wordweight = 0
            scoreS = scoreS + wordweight
	#print "S score:"+str(scoreS)
        scoreB = 0
        for k in B: #same procedure to evaluate score for B
            if "-" not in B[k]:
		if B[k] in weight_dict[k]:
                    wordweight = weight_dict[k][B[k]]
                else:
                    wordweight = 0
            else:
                wordweight = 0
            scoreB = scoreB + wordweight
	#print "B score:"+str(scoreB)
        if scoreS > scoreB:
            return S
        else:
            return B

    #determine variables yet to be assigned
    unassigned_vars = list( set(variables) - set(S.keys()) )

    #v is variable with max difference, d is the highest scoring word; not in P
    max_difference = 0
    i = 0 #initialize variable for which word to pick
    for k in unassigned_vars:
        #calculate score difference between 1st and 2nd candidate
        if len(domains[k]) == 0: #if no words are in the domain, fill with "----"
            S[k] = '-'*puz.entries[k].length
            for k in S.keys():
                S = puz.update_solution(S,k)
            return solve(puz,domains,neighbors,S,B,n,P,variables,weight_dict)

        elif len(domains[k])>1:
            #have to limit to words not in P
            wordinP = True
            while wordinP == True:
		if k in P:
		    if len(domains[k]) == len(P[k])-2: #if there are only 2 words left to pick from in the domain
			i = len(domains[k]) - 2
			first_score = weight_dict[k][domains[k][i]]
			wordinP = False	
		    elif i == len(domains[k]): #if you've reached the end of the domain candidates, fill with "--"
			S[k] = '-'*puz.entries[k].length
            		for k in S.keys():
                	    S = puz.update_solution(S,k)
            		return solve(puz,domains,neighbors,S,B,n,P,variables,weight_dict)
                    elif domains[k][i] in P[k]: #check to see if word has been pictched
                    	i += 1 #if so, try the next word in the domain
                        wordinP = True
		    else: #if the word hasn't been pitched before
			first_score = weight_dict[k][domains[k][i]]
			wordinP = False
                else: #if the variable doesn't exist in P (not relevant anymore since P is preloaded)
		    first_score = weight_dict[k][domains[k][i]]
                    wordinP = False
	    #end of while loop

	    #if you're at the end of the domain, there's no second highest word
	    if i == len(domains[k])-1:
		second_score = 0
	    else:
            	second_score = weight_dict[k][domains[k][i+1]]

        else: #if the length of the domain is only 1 word long
	    if domains[k][0] in P[k]: #if the only word has been pitched, fill
		S[k] = '-'*puz.entries[k].length
            	for k in S.keys():
                    S = puz.update_solution(S,k)
            	return solve(puz,domains,neighbors,S,B,n,P,variables,weight_dict)
	    else:
            	first_score = weight_dict[k][domains[k][0]]
            	second_score = 0
	#calculate the difference and select the highest word
        difference = abs(first_score - second_score)
        if difference >= max_difference:
            max_difference = difference
            v = k #**assigning v = variable**
            d = domains[k][i] #**assigning d = word**

	
    #S' = S plus the assignment of v to d
    #C' = propogation of assignment of v to d in C, ie updating domains
    #testing to see if v interferes with neighbors
    success, next_domains, next_S = propagate(v,d,puz,domains,neighbors,S)

    #if C' is still valid
    if success == True:
        B = solve(puz,next_domains,neighbors,next_S,B,n,P,variables,weight_dict)


    #print P
    #C' not valid
    #if the size of P is less than n, add d to pitched words, loop again
    Plength = 0
    for k in P.keys(): #calculate size of P
	Plength += len(P[k])
    if Plength < n:
        P[v].append(d)
        B = solve(puz,domains,neighbors,S,B,n,P,variables,weight_dict)
    #print B
    return B

def solve_recursive(puz,variables,domains,neighbors,S,weight_dict):
   
    #initialize P with list of variables
    P = {} 
    for var in variables:
	P[var] = []

    B = {}

    soln = solve(puz,domains,neighbors,S,B,n,P,variables,weight_dict)

    return soln

## Find a solution to the puzzle
def solve_puzzle(puz,component_output,mode,limit,score_adjust,second_round=True):
    if puz.is_rebus:
        raise RebusError("Solver cannot handle rebus style puzzles")

    puz.update_all_intersections()
    domains,weight_dict,unanswered_clues = generate_all_candidates(puz,limit,score_adjust,component_output)

    # construct CSP problem
    problem = csp.CSP(puz.entries.keys(),
                      domains,
                      {k:puz.entries[k].intersections.keys() for k in puz.entries.keys()},
                      puz.check_intersect)
    variables = puz.entries.keys()
    neighbors = {k:puz.entries[k].intersections.keys() for k in puz.entries.keys()}
    S = {}

    # assign variables which cannot be answered
    for k in unanswered_clues:
        S[k] = domains[k][0] # this will be "-"*
        domains.pop(k)

    print "\nSolving CSP probelm ....."
    start = time.time()
    solution = solve_recursive(puz,variables,domains,neighbors,S,weight_dict)
    #print solution
    end = time.time()
    print("\nCSP solver runtime: " + str(end-start))

    # evaluate solution
    print "\nEvaluating solution ...."
    evaluation = puz.evaluate_solution(problem,solution,'_before_fill')
    evaluation['runtime_before_fill'] = end-start

    # PART 2 GOES HERE - FILL IN BLANK SQUARES

    # UNCOMMENT THESE LINES WHEN NEEDED
    #print "\nEvaluating filled solution ...."
    #evaluation = puz.evaluate_solution(problem,solution,'_after_fill')

    end2 = time.time()
    print("\nBlank square filling runtime: " + str(end2-start))
    evaluation['runtime']=end2-start

    return evaluation,solution

## Handle command line arguments
def arg_parse():
    parser = argparse.ArgumentParser(description="Import a .puz file as a python puzzle obect and output a solution.")
    parser.add_argument('puz_file', metavar='puz_file', type=str,
                        help='path to the .puz file to load')
    parser.add_argument('candidates_file', metavar='candidates_file', type=str,
                        help='path to component output to use when generating candidate answers')
    return parser.parse_args()

if __name__ == "__main__":
    args = arg_parse()
    p = puzzle.Puzzle(args.puz_file)
    evaluation = solve_puzzle(p,open(args.candidates_file).read())
    print p.get_side_by_side_comparison()
    for k,v in sorted(evaluation.items()):
        print k+':'+'\t'+str(v)

