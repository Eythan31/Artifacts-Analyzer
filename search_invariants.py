###################################################
# Script for finding invariants in a CSV file of artifacts
# containing boolean (TRUE/FALSE) variables and categorial 
# variables (ex: color, material, etc...). 
# Numerical values should not be used.
# Column names should not contain spaces.
# Values can also be "UNKNOWN" (without the quotes).

# PARAMETERS (defined in the code hereunder) :
#   -INPUT_FILE: name of the input file (in the same directory as this file)
#   -ABS_THRESHOLD: "absolute threshold": the minimum required percentage for invariants (between 0 and 100)
#   -RELATIVE_THRESHOLD: Also called "relevance ratio". The minimum ratio between the percentage of this invariant (say "A => B") and the 
#       "complementary" invariant (say "NOT(A) => B"). This is a parameter of "relevance", saying if the 
#       invariant is "relevant" to the predicate "A" or if we observe the same among the other items ("NOT(A)").
#       Use the value 1 (for no threshold) or values above 1.
#   -MIN_NBR_ITEMS: minimum number of items (artifacts) for which this invariant holds (use 1 in case you do    
#       not want a minimum)
#   -CSV_DELIMITER: the CSV delimiter: typically, comma or semicolon

# USAGE: run this file and the results get printed to screen

# ALTERNATIVE USAGE (for having the result in a file "result.txt",
#   by using output redirection): open a terminal and type:
#   python search_invariants.py > results.txt


########################################
## PARAMETERS (TO BE SET BY THE USER) ##
########################################
INPUT_FILE = "seals-2022-08-31.csv"
ABS_THRESHOLD = 80  #Relevance ratio
RELATIVE_THRESHOLD = 1.2
MIN_NBR_ITEMS = 5
CSV_DELIMITER = ","
REMOVE_FIRST_COLUMN = True #in case the first column contains an identifier which should not be used in the search for invariants (otherwise, use False)
########################################


###################################################################
############# DO NOT MODIFY THE CODE BELOW THIS POINT #############
###################################################################

########################################
import csv
from datetime import datetime

########################################
INPUT_FILE_ALL_BOOLS = "input-all-booleans.csv"
########################################

#####################################################
#New version, totally automated. Automatically detects categorial
#columns, erases them and replaces them with booleans.
#####################################################

def analyze(inputFileName, outputFileName):    
    print_headers()
    new_list=prepare_data(inputFileName)
    testAll(new_list)


def print_headers():
    print("\t\tInvariant search")    
    print("\t\t================")    
    print()
    print("Parameters:")
    print("===========")      
    dateTimeObj = datetime.now()
    print("Date & time: ",dateTimeObj.day, '/', dateTimeObj.month, '/', dateTimeObj.year, ", ",dateTimeObj.hour, ':', dateTimeObj.minute, ':', dateTimeObj.second, sep='')
    print("Input file: ", INPUT_FILE)
    print("Absolute threshold: ", ABS_THRESHOLD, "%")
    print("Relevance ratio: ", RELATIVE_THRESHOLD)
    print("Min. number of items: ", MIN_NBR_ITEMS)
    print()


def prepare_data(inputFileName):
    my_list = read_csv_to_list(inputFileName)
    if(REMOVE_FIRST_COLUMN):
        delete_first_column(my_list)
    convertMissingDataToUnknown(my_list)    
    new_list=convertCategoriesToBooleanStrings(my_list)    
    new_list=convertStringsToBooleans(new_list)
    write_list_to_csv(new_list, "processed_data_2.csv") #for checking purposes
    return new_list    
    
def delete_first_column(list_2D):
    for j in list_2D:
        del j[0]


def read_csv_to_list(inputFileName):    
    with open(inputFileName, newline='') as f:
        reader = csv.reader(f, delimiter=CSV_DELIMITER)
        my_list= list(reader)
    return my_list
    
            
def convertStringsToBooleans(my_list):
    new_list=[]
    new_list.append(my_list[0]) 
    for i in range(1, len(my_list)):
        new_list.append([])
        for j in range(0, len(my_list[i])):                        
            new_list[i].append(toBool(my_list[i][j]))
    return new_list

    
def write_list_to_csv(my_list, fileName)    :
    with open(fileName, 'w') as f: 
        write = csv.writer(f, delimiter=CSV_DELIMITER) 
        write.writerow(my_list[0]) 
        write.writerows(my_list[1:]) 
    
def convert_to_uppercase(my_list):
    for i in range(1,len(my_list)):    
        for j in range(len(my_list[i])):
            my_list[i][j] = my_list[i][j].upper()
    
def convertCategoriesToBooleanStrings(my_list):
    names = my_list[0]
    #create empty rows in new list
    new_list=[]
    for i in range(len(my_list)):
        new_list.append([])
     
    for j in range(len(names)):#for each column   
        if not column_is_categorial(my_list, j): #if boolean column, copy the column            
            for i in range(0,len(new_list)):
                new_list[i].append(my_list[i][j])
        else:            
            values = get_all_categorial_values(my_list, j)            
            for value in values:
                new_list[0].append(my_list[0][j]+"="+value)
            for i in range(1,len(my_list)):
                value_in_row = my_list[i][j]
                for value in values:
                    if value_in_row=="UNKNOWN":
                        new_list[i].append("UNKNOWN")
                    elif value_in_row==value:                        
                        new_list[i].append("TRUE")      
                    else:
                        new_list[i].append("FALSE")  
    return new_list
                    

def get_all_categorial_values(my_list, col_index):
    values = []
    for i in range(1,len(my_list)):
        values.append(my_list[i][col_index])
    values = list( dict.fromkeys(values) ) #remove duplicates
    if("UNKNOWN" in values):
        values.remove("UNKNOWN")            
    return values

#For checking/debugging purposes                
def check_column_types(myList):        
    names = myList[0]
    for i in range(len(names)):
        print(names[i], " is ", end="")
        if column_is_categorial(myList, i):
            print("categorial")
        else:
            print("boolean")

               
def column_is_categorial(myList, col_index):
    allowed_strings = ["TRUE", "FALSE", "UNKNOWN"]
    for i in range(1,len(myList)):
        if not(myList[i][col_index].upper() in allowed_strings):
            return True
    return False


def print_list_as_csv(my_list):
    error=False
    first_length=len(my_list[0])
    print("nbr of columns = ", first_length)
    for i in range(len(my_list)):
        print(i, end=": " )
        for j in range(len(my_list[i])):
            print(my_list[i][j], end=CSV_DELIMITER )
        if len(my_list[i]) != first_length :
            error=True
            error_line=i            
        print()
    if error:
        print("  Error:, line ", error_line, "has different length: ", len(my_list[i]), "!!!")
    
    
def convertMissingDataToUnknown(my_list):        
    for i in range(len(my_list)):
        for j in range(len(my_list[i])):
            if my_list[i][j].upper() == "TBD" or my_list[i][j] == "" or  ("?" in my_list[i][j]):
                my_list[i][j] = "UNKNOWN"

############################################################
# checks if boolean value A implies boolean value B using the
# standard logical definition of implication: NOT(A) OR B 
#############################################################
def implies(A,B):
    return not(A) or B

############################################################
# Converts a string containing "True", "False" or "Unknown" 
# (independently of the case) to Python boolean values True, 
# False or None, respectively.
# In other cases, return None.
############################################################
def toBool(string):
    string = string.upper()#convert to uppercase
    if string=="TRUE":
        return True
    elif string == "FALSE":
        return False
    elif string == "UNKNOWN":
        return None
    else: #Wrong boolean value
        return None


def applyPredicate(boolean, predicate) :
    if predicate:
        return boolean
    else:
        return not boolean
    
####################################                                
def AimpliesBpercent(my_list, A,B, predA=True, predB=True, percents=100, relative_threshold=0, min_nbr_items=0):
    titles = my_list[0] #= lines[0].rstrip().split(";")    
    header=""    
    if not predA:
        header += "NOT("
    header += titles[A] 
    if not predA:
        header += ")"
    header +=" => "
    if not predB:        
        header += "NOT("    
    header += titles[B] 
    if not predB:
        header += ")"
    header += " ?"
    
    result=True
    falses=0
    falsesCompl=0
    total=0
    totalTrue=0
    totalTrueCompl=0
    
    for x in my_list[1:]:        
        a = x[A]
        b = x[B]   
        if a != None and b != None and not implies(applyPredicate(a, predA), applyPredicate(b, predB)) :#BUG:c'est pas un AND
            falses+=1        
        if a != None and b != None and not implies(applyPredicate(a, not predA), applyPredicate(b, predB)) :
            falsesCompl+=1   
        if a != None and b != None :
            total +=1
            if applyPredicate(a, predA):
                totalTrue += 1
            if applyPredicate(a, not predA):
                totalTrueCompl += 1

    result=""
    
    if totalTrue != 0 :
        result2=""
        header2 = ("NOT(" if predA else "") + titles[A] + (") " if predA else " ") + "=> " + ("NOT(" if not predB else "") + titles[B] + (") " if not predB else " ")+ " ?"
        percentage = (1-(falses/totalTrue))*100 #avec totalTrue plutôt que total
        result += "  "  + str(round(percentage)) +"%" + " (" + str(totalTrue-falses) + "/" + str(totalTrue) +  ")"
        #result += " (vs " + str(round(percentsOf(my_list, B, predB))) + "% of " + ("NOT " if not predB else "") + str(titles[B]) + ")" 
        if totalTrueCompl != 0:
            percentageCompl = (1-(falsesCompl/totalTrueCompl))*100 #avec totalTrue plutôt que total
            #result2 += " (vs " + str(totalTrueCompl-falsesCompl) + "/" + str(totalTrueCompl) + " = " + str(round(percentageCompl)) + "% among " + ("NOT " if predA else "") + str(titles[A]) + ")" 
            result2 +=  "" + str(round(percentageCompl)) + "%" + " (" +str(totalTrueCompl-falsesCompl) + "/" + str(totalTrueCompl) + ")"
        else:
            percentageCompl = 0
            #result2 += " (vs " + str(totalTrueCompl-falsesCompl) + "/" + str(totalTrueCompl) + " among " + ("NOT " if predA else "") + str(titles[A]) + ")" 
            result2 += str(totalTrueCompl-falsesCompl) + "/" + str(totalTrueCompl) + "%"
        #for a=>B , I need percentage of B among NON(A), that is number of number of B/NON(A)? Le denominateur c'est total-totalTrue. LE numerateur c'est 
        
        #NOTE:  I do not include an invariant "A => B" if it has a smaller percentage than "NOT(A) => B"
        ratio=0
        if min(percentage, percentageCompl) != 0:
            #ratio = abs(max(percentage, percentageCompl)/min(percentage, percentageCompl))
            ratio = percentage/percentageCompl
        else: 
            ratio = 999999
        if percentage >= percents and ratio >= relative_threshold and totalTrue >= min_nbr_items: 
            if ratio != 999999:          
                return (header + result + "\n" + "\t\t" + header2 + " " + result2, round(percentage))
                
        return ("",0)
        
    else:
        percentage=0
        result= titles[A] + " is never True"           
        return ("",0)

#Faut virer les unknown ici aussi , si pas déjà fait!
def percentsOf(my_list, A, predA):    
    true=0
    total=0
    for x in my_list[1:]:
        a = x[A]
        if a != None:
            total +=1
            if applyPredicate(a, predA):
                true+=1
    return true/total*100


def testAll(my_list):
    print("Absolute invariants")
    print("===================")
    i=1
    dic={}
    for col1 in range(len(my_list[0])): #for each pair of columns                       
        for col2 in range(len(my_list[0])):                        
            if col1 != col2 : # do not compare a column to itself
                name1 = my_list[0][col1]
                name2 = my_list[0][col2]
                if not("=" in name1 and "=" in name2 and name1.split('=')[0] == name2.split('=')[0]) : # do not compare categorical columns (those having an equality sign) if they have the same prefix
                    (inv, perc) = AimpliesBpercent(my_list, col1, col2, True,True, ABS_THRESHOLD, RELATIVE_THRESHOLD, MIN_NBR_ITEMS )
                    i = printInvariantResult(inv, perc, i, dic)

                    (inv, perc) = AimpliesBpercent(my_list, col1, col2, True,False, ABS_THRESHOLD, RELATIVE_THRESHOLD, MIN_NBR_ITEMS )                    
                    i = printInvariantResult(inv, perc, i, dic)
                    
                    (inv, perc) = AimpliesBpercent(my_list, col1, col2, False, True, ABS_THRESHOLD, RELATIVE_THRESHOLD, MIN_NBR_ITEMS )
                    i = printInvariantResult(inv, perc, i, dic)                      

                    (inv, perc) = AimpliesBpercent(my_list, col1, col2, False, False, ABS_THRESHOLD, RELATIVE_THRESHOLD, MIN_NBR_ITEMS )
                    i = printInvariantResult(inv, perc, i, dic)
    
    
    print("Non-absolute invariants (sorted)")
    print("================================")                    
    for key, value in  sorted(dic.items(), reverse=True):
        for inv in value:
            print(str(i), ". ", end='', sep='')
            i+=1
            print(inv)
            print()

def printInvariantResult(inv, perc, i, dic):
    if(inv!=""):
        if(perc==100): #absolute invariant get printed first
            print(str(i), ". ", end='', sep='')
            i+=1
            print(inv)
            print()
        else:
            if perc in dic:
                dic[perc].append(inv)
            else:
                dic[perc]=[inv]
    return i

################################################                       
################ MAIN ##########################                       
################################################
analyze(INPUT_FILE, INPUT_FILE_ALL_BOOLS)                
################################################
