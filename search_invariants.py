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
INPUT_FILE = "seals-ABRIDGED-2023-07-31.csv"#"seals-ABRIDGED-2023-07-31.csv"
ABS_THRESHOLD = 75
RELATIVE_THRESHOLD = 2 #Relevance ratio for invariants
MIN_NBR_ITEMS = 4
MIN_NBR_ITEMS_CONTRASTS = 5 #minimun nbr of items for inclusion in contrast table when one of the invariants as 0 occurrences
CSV_DELIMITER = ","
REMOVE_FIRST_COLUMN = True #in case the first column contains an identifier which should not be used in the search for invariants (otherwise, use False)
NEGATE_CATEGORICAL_VARIABLES = False #should categorical variables be negated as well or only boolean variables
DO_NOT_NEGATE_FIRST_VARIABLE = True #do not search for invariants of the shape NOT(A) => B and NOT(A) => NOT(B)
#Contrasts:
CONTRAST_BY_RATIO = False
RELATIVE_THRESHOLD_CONTRASTS = 1.5 #Relevance ratio for contrasts
CONTRAST_BY_SKIPPING = True
CONTRASTS_SKIPPED_CLASSES = 1 # Minimum number of classes to be skipped to be considered as a contrast (0 if none to be skipped)
CONTRAST_BY_GAP = False # Do we want sliding contrast gaps?
SLIDING_CONTRASTS_GAP = 25#Sliding contrasts gap, in percents
#CONTRAST_THRESHOLD = 75 # threshold for contrasting invariants (for the "MOSTLY/USUALLY" category)
########################################


###################################################################
############# DO NOT MODIFY THE CODE BELOW THIS POINT #############
###################################################################

########################################
import csv
from datetime import datetime
import networkx as nx
import matplotlib.pyplot as plt
#import numpy as np

########################################
INPUT_FILE_ALL_BOOLS = "input-all-booleans.csv"
########################################

#####################################################
#New version, totally automated. Automatically detects categorial
#columns, erases them and replaces them with booleans.
#####################################################

GEOGRAPHICAL_KEYWORDS = ["polity", "city", "country", "region", "provenance", "land"]
ADJECTIVES = ["iconic", "pierced", "perforated", "divided", "bordered", "painted", "colored", "coloured", "burnished"]

all_categ_columns = []
all_boolean_columns = []
abs_invariants = {}
abs_invariants_cols = []

class Invariant:
    
    def __init__(self, bool_matrix, col1Bool, col2Bool, predicate1=True, predicate2=True):
        self.bool_matrix = bool_matrix
        self.col1Bool = col1Bool # example: iconic
        self.col2Bool = col2Bool # example: polity=Judah
        self.col1 = get_var_name(col1Bool) # example: iconic
        self.col2 = get_var_name(col2Bool) # example: polity
        self.predicate1 = predicate1 # True or False (ex: for "iconic" or "not iconic")
        self.predicate2 = predicate2# True or False (ex: for "polity=Judah" or "not (polity=Judah)")
        self.countRowsWithoutNone = 0
        self.countLeftIsTrue = 0
        self.aANDb = 0
        self.initStats()
        self.ALWAYS = "always"
        self.MOSTLY = "mostly"
        self.OFTEN = "often"
        self.OCCASIONALLY = "occasionally"
        self.RARELY = "rarely"
        self.NEVER = "never"
        self.ALWAYS_PERCENTAGE = 100
        self.MOSTLY_THRESHOLD = 75
        self.OFTEN_THRESHOLD = 50
        self.OCCASIONALLY_THRESHOLD = 25
        self.RARELY_THRESHOLD = 0
        self.NEVER_PERCENTAGE = 0
        
    def initStats(self):
        try:
            index_1 = self.bool_matrix[0].index(self.col1Bool)
        except:
            print(self.bool_matrix[0])
            print(self.col1Bool)
        index_2 = self.bool_matrix[0].index(self.col2Bool)
        for row in self.bool_matrix[1:]:        
            a = row[index_1]
            b = row[index_2]   
            if a != None and b != None:
                self.countRowsWithoutNone +=1                    
                if applyPredicate(a, self.predicate1):
                    self.countLeftIsTrue += 1
                if applyPredicate(a, self.predicate1) and applyPredicate(b, self.predicate2) :
                    self.aANDb += 1  

    def getPercentage(self):
        if self.countLeftIsTrue == 0:
            return 0
        return round(self.aANDb/self.countLeftIsTrue*100)
    
    def getPercentageAndFraction(self):
        if self.countLeftIsTrue ==0:
            return "0% (0/0)"
        else:
            return str(self.getPercentage()) +"%" + " (" + str(self.aANDb) + "/" + str(self.countLeftIsTrue) +  ")"

    def getFractionAndPercentage(self):
        if self.countLeftIsTrue ==0:
            return "0% (0/0)"
        else:
            return str(self.aANDb) + "/" + str(self.countLeftIsTrue) +  " = " + str(self.getPercentage()) +"%" 
        
        def get_header(self, my_list, A,B, predA, predB):
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
            return header
    
    def get_header_left(self):        
        header=""    
        if not self.predicate1 :
            header += "NOT("
        header += self.col1Bool 
        if not self.predicate1 :
            header += ")"        
        return header
    
    def getLeftEnglish(self):
        result = ""
        if self.col1.lower() in GEOGRAPHICAL_KEYWORDS:
            if self.predicate1:
                result += "Artifacts FROM "+ get_var_value(self.col1Bool)
            else:
                result += "Artifacts NOT FROM "+ get_var_value(self.col1Bool)
        elif self.col1.lower() in ADJECTIVES:
            if self.predicate1:
                result += self.col1 + " artifacts"
            else:
                result += "NON-" + self.col1 + " artifacts"
        elif self.col1 in all_boolean_columns: #if it is otherwise boolean
            if self.predicate1:
                result += "Artifacts WITH " + self.col1
            else:
                result += "Artifacts WITHOUT " + self.col1
        else: # categorical variables
            if self.predicate1:
                result += "Artifacts WITH " + get_var_value(self.col1Bool) + " " + self.col1 
            else:
                result += "Artifacts WITHOUT " + get_var_value(self.col1Bool) + " " + self.col1 
        return result
    
    def getRightEnglish(self):        
        if self.col2.lower() in GEOGRAPHICAL_KEYWORDS:
            if self.predicate2:
                return "ARE FROM "+ get_var_value(self.col2Bool)
            else:
                return "ARE NOT FROM "+ self.col2 + get_var_value(self.col2Bool)
        # Adjectives
        if self.col2.lower() in ADJECTIVES:
            if self.predicate2:
                return "ARE "+ self.col2
            else:
                return "ARE NON-" + self.col2
        # Boolean columns that were not identified as adjectives
        if self.col2 in all_boolean_columns: #if it is otherwise boolean
            if self.predicate2:
                return "ARE WITH " + self.col2
            else:
                return "ARE WITHOUT " + self.col2
        # categorical variables that were not identified as geographical
        else: 
            if self.predicate2:
                return "HAVE " + get_var_value(self.col2Bool) + " " + self.col2 
            else:
                return "HAVE NO " + get_var_value(self.col2Bool) + " " + self.col2 
    
            
    def get_header_right(self):
        header=""    
        if not self.predicate2:        
            header += "NOT("    
        header += self.col2Bool 
        if not self.predicate2:
            header += ")"
        return header
        
    def getMathView(self):
        index_1 = self.bool_matrix[0].index(self.col1Bool)
        index_2 = self.bool_matrix[0].index(self.col2Bool)
        header = self.get_header(self.bool_matrix, index_1, index_2, self.predicate1, self.predicate2) 
        result = "  "  + str(self.getPercentage()) +"%" + " (" + str(self.aANDb) + "/" + str(self.countLeftIsTrue) +  ")"
        return header + result
    
    def getEnglishView(self):
        return self.getLeftEnglish() + " " + self.getRightEnglish()
    
    def getNbrOfAttestations(self):
        return self.aANDb
        
    def getFraction(self):
        return str(self.aANDb) + "/" + str(self.countLeftIsTrue)    
    
    def getCol1(self):
        return self.col1
    
    def getCol2(self):
        return self.col2
    
    def frequencyLabel(self):
        if self.getPercentage() == self.ALWAYS_PERCENTAGE:
            return self.ALWAYS
        elif self.getPercentage() >= self.MOSTLY_THRESHOLD:
            return self.MOSTLY
        elif self.getPercentage() >= self.OFTEN_THRESHOLD:
            return self.OFTEN
        elif self.getPercentage() > self.OCCASIONALLY_THRESHOLD:
            return self.OCCASIONALLY
        elif self.getPercentage() > self.RARELY_THRESHOLD:
            return self.RARELY
        else:
            return self.NEVER
        
    def getFrequencyAsRank(self): #returns the frequency as an integer (NEVER=0, ALWAYS=5)
        if self.frequencyLabel() == self.ALWAYS:
            return 5
        elif self.frequencyLabel() == self.MOSTLY:
            return 4
        elif self.frequencyLabel() == self.OFTEN:
            return 3
        elif self.frequencyLabel() == self.OCCASIONALLY:
            return 2
        elif self.frequencyLabel() == self.RARELY:
            return 1
        elif self.frequencyLabel() == self.NEVER:
            return 0
    
    def contrastsTo(self, other):
        freq1 = self.frequencyLabel()
        freq2 = other.frequencyLabel()
        return  self.countLeftIsTrue != 0 and other.countLeftIsTrue != 0 and\
                (CONTRAST_BY_SKIPPING and (abs(self.getFrequencyAsRank() - other.getFrequencyAsRank()) > CONTRASTS_SKIPPED_CLASSES) or \
                (CONTRAST_BY_GAP and abs(self.getPercentage() - other.getPercentage()) > SLIDING_CONTRASTS_GAP) or\
                # ((freq1 == self.ALWAYS and freq2 == self.OCCASIONALLY) or \
                # (freq1 == self.ALWAYS and freq2 == self.RARELY) or \
                # (freq1 == self.ALWAYS and freq2 == self.NEVER) or \
                # (freq1 == self.ALWAYS and freq2 == self.OFTEN) or \
                # (freq1 == self.MOSTLY and freq2 == self.OCCASIONALLY) or \
                # (freq1 == self.MOSTLY and freq2 == self.RARELY) or \
                # (freq1 == self.MOSTLY and freq2 == self.NEVER) or \
                # (freq1 == self.OFTEN  and freq2 == self.RARELY) or \
                # (freq1 == self.OFTEN  and freq2 == self.NEVER) or\
                # (freq2 == self.ALWAYS and freq1 == self.OCCASIONALLY) or \
                # (freq2 == self.ALWAYS and freq1 == self.RARELY) or \
                # (freq2 == self.ALWAYS and freq1 == self.NEVER) or \
                # (freq2 == self.MOSTLY and freq1 == self.OCCASIONALLY) or \
                # (freq2 == self.MOSTLY and freq1 == self.RARELY) or \
                # (freq2 == self.MOSTLY and freq1 == self.NEVER) or \
                # (freq2 == self.OFTEN  and freq1 == self.RARELY) or \
                # (freq2 == self.OFTEN  and freq1 == self.NEVER) or\
                # (freq1 == self.OCCASIONALLY and freq2 == self.NEVER) or \
                (CONTRAST_BY_RATIO and self.getFrequencyAsRank() != other.getFrequencyAsRank()\
                      and min(self.getPercentage(),other.getPercentage())>0 \
                      and max(self.getPercentage(),other.getPercentage())/min(self.getPercentage(),other.getPercentage()) > RELATIVE_THRESHOLD_CONTRASTS)) #or\
                #(min(self.getPercentage(),other.getPercentage())==0 and max(self.getNbrOfAttestations(),other.getNbrOfAttestations()) > MIN_NBR_ITEMS_CONTRASTS)) 



############################################################
# Print a header representing all the parameters of the
# experiment.
############################################################
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

############################################################
# Reads the input file and returns a matrix (list of lists) 
# of booleans containing the same data. Each column of the
# matrix represents a boolean expression like "Iconic" or
# like "Material=Stone". Each row represents a seal. Each
# cell is a boolean value: True, False or None. 
############################################################
def prepare_data(inputFileName, outputFileName):
    my_list = read_csv_to_list(inputFileName)
    if(REMOVE_FIRST_COLUMN):
        delete_first_column(my_list)
    convertMissingDataToUnknown(my_list)    
    new_list = convertCategoriesToBooleanStrings(my_list)    
    new_list = convertStringsToBooleans(new_list)
    write_list_to_csv(new_list, outputFileName) #for checking purposes
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
    new_list = []
    for i in range(len(my_list)):
        new_list.append([])
     
    for j in range(len(names)): # for each column   
        if not column_is_categorial(my_list, j): # if boolean column, copy the column
            all_boolean_columns.append(my_list[0][j])
            for i in range(0,len(new_list)):
                new_list[i].append(my_list[i][j])
        else:            
            values = get_all_categorial_values(my_list, j)            
            for value in values:
                new_list[0].append(my_list[0][j]+"="+value)
                all_categ_columns.append(my_list[0][j]+"="+value)
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

################################################################
# Takes a boolean value and applies a True/False predicate to it
################################################################
def applyPredicate(boolean, predicate) :
    if predicate:
        return boolean
    else:
        return not boolean
    
def get_header(my_list, A,B, predA, predB):
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
    return header
    
###############################################################################
# Check if the invariant "predA(A) => predB(B)" holds,
# with the following additional constraints:
#   -The proportion of items where predB(B) is True among those where predA(A) is True must be at least "percents" percents               
#   -The relative threshold must be at least "relative_threshold"
#   -The invariant must hold for at least "min_nbr_items" items
# Returns a string representing the invariant, as well as the corresponding percentage
# Returns an empty string and 0 if the invariant does not hold with the required constraints
###############################################################################
def AimpliesBpercent(bool_matrix, A,B, predA=True, predB=True, percents=100, relative_threshold=0, min_nbr_items=0):       
    titles = bool_matrix[0] #= lines[0].rstrip().split(";")   
    result=True
    falses=0 # number of cases where A does not imply B
    falsesCompl=0 # number of cases where NOT(A) does not imply B
    total=0 # total nulber of cases where the invariant could be evaluated
    totalTrue=0 # number of cases where A is true
    totalTrueCompl=0 #number of cases where NOT(A) is true
    trues=0
    aANDb = 0

    for row in bool_matrix[1:]:        
        a = row[A]
        b = row[B]   
        if a != None and b != None:
            total +=1
            if applyPredicate(a, predA) and applyPredicate(b, predB) :
                aANDb += 1  
            if implies(applyPredicate(a, predA), applyPredicate(b, predB)) :
                trues += 1  
            if not implies(applyPredicate(a, predA), applyPredicate(b, predB)) :
                falses += 1        
            if not implies(applyPredicate(a, not predA), applyPredicate(b, predB)) :
                falsesCompl+=1                           
            if applyPredicate(a, predA):
                totalTrue += 1
#            if applyPredicate(a, not predA):
#                totalTrueCompl += 1

    totalTrueCompl = total - totalTrue
    result=""
#    print("********* total=",total,", falses=",falses,", falsesCompl=", falsesCompl, ", totalTrue=", totalTrue, ", totalTrueCompl=", totalTrueCompl, ", trues=", trues, ", aANDb=", aANDb, end="")
#    if totalTrue != 0 :
#        print(", perc=", (1-(falses/totalTrue))*100 )
#    else:
#        print()
    
    if totalTrue != 0 :
        result2=""
        header2 = ("NOT(" if predA else "") + titles[A] + (") " if predA else " ") + "=> " + ("NOT(" if not predB else "") + titles[B] + (") " if not predB else " ")+ " ?"
        percentage = (1-(falses/totalTrue))*100  
        result += "  "  + str(round(percentage)) +"%" + " (" + str(totalTrue-falses) + "/" + str(totalTrue) +  ")"
        if totalTrueCompl != 0:
            percentageCompl = (1-(falsesCompl/totalTrueCompl))*100 #avec totalTrue plutôt que total
            result2 +=  "" + str(round(percentageCompl)) + "%" + " (" +str(totalTrueCompl-falsesCompl) + "/" + str(totalTrueCompl) + ")"
        else:
            percentageCompl = 0
            result2 += str(totalTrueCompl-falsesCompl) + "/" + str(totalTrueCompl) + "%"
        
        #NOTE:  I do not include an invariant "A => B" if it has a smaller percentage than "NOT(A) => B"
        ratio=0
        if min(percentage, percentageCompl) != 0:
            ratio = percentage/percentageCompl
            ratio2 = (totalTrue-falses)/total*100 if total != 0 else 0 #number of trues divider by total number on which the invariant could be tested.
        else: 
            ratio = 999999
            ratio2 = 999999
        if percentage >= percents and ratio >= relative_threshold and totalTrue >= min_nbr_items: 
            if ratio != 999999:     
                header = get_header(bool_matrix, A,B, predA, predB) 
                #return (header + result + "\n" + "\t\t" + header2 + " " + result2 + "\n\t\t Relevance ratio: "+ str(ratio2) , round(percentage))
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
                    #print(inv2.getMathView)
                    if(perc == 100):
                        #INV = Invariant(my_list, name1, name2, True, True)
                        #print(str(i-1), ". ", end='', sep='')
#                        print(INV.getMathView())
#                        INV_CPL = Invariant(my_list, name1, name2, False, True)
#                        print("\t\t", INV_CPL.getMathView())
                        print()
                    if perc >= ABS_THRESHOLD:
                        if not name1 in abs_invariants_cols:
                            abs_invariants_cols.append(name1)
                        if not name2 in abs_invariants_cols:
                            abs_invariants_cols.append(name2)
                        if name1 in abs_invariants:
                            abs_invariants[name1].append(name2)
                        else:
                            abs_invariants[name1] = [name2]

                    if NEGATE_CATEGORICAL_VARIABLES or (name2 not in all_categ_columns):
                        (inv, perc) = AimpliesBpercent(my_list, col1, col2, True,False, ABS_THRESHOLD, RELATIVE_THRESHOLD, MIN_NBR_ITEMS )                    
                        i = printInvariantResult(inv, perc, i, dic)
                        if(perc == 100):
                            #INV = Invariant(my_list, name1, name2, True, False)
                            #print(str(i-1), ". ", end='', sep='')
#                            print(INV.getMathView())
#                            INV_CPL = Invariant(my_list, name1, name2, False, False)
#                            print("\t\t", INV_CPL.getMathView())
                            print()
                        if perc >= ABS_THRESHOLD:
                            if not name1 in abs_invariants_cols:
                                abs_invariants_cols.append(name1)
                            if not ("NOT "+ name2) in abs_invariants_cols:
                                abs_invariants_cols.append(("NOT "+ name2))
                            if name1 in abs_invariants:
                                abs_invariants[name1].append(("NOT "+ name2))
                            else:
                                abs_invariants[name1] = [("NOT "+ name2)]

                    if not DO_NOT_NEGATE_FIRST_VARIABLE:
                        if NEGATE_CATEGORICAL_VARIABLES or (name1 not in all_categ_columns):
                            (inv, perc) = AimpliesBpercent(my_list, col1, col2, False, True, ABS_THRESHOLD, RELATIVE_THRESHOLD, MIN_NBR_ITEMS )
                            i = printInvariantResult(inv, perc, i, dic)                      
    
                        if NEGATE_CATEGORICAL_VARIABLES or (name2 not in all_categ_columns and name1 not in all_categ_columns) :
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
            
def findAllAbsoluteInvariants(my_list, min_nbr_items):
    invs, invs_cpl = testAllInvariants(my_list, min_nbr_items)     
    return invs

def findAllNonAbsoluteInvariants(my_list, min_nbr_items, abs_threshold):
    invs, invs_cpl = testAllInvariants(my_list, min_nbr_items, abs_threshold)
    return invs

#returns a list of invariants and a list of complementary invariants (A=>B and NOT(A)=>B)
def findAllMoreOftenThanInvariants(my_list, min_nbr_items, rel_threshold):
    return testAllInvariants(my_list, min_nbr_items, 0, rel_threshold)

##################################################
# Find all invariants (helper function for the above 3 functions)
# Parameter: boolean matrix
# Returns a list of Invqriqnt objects  
# Add parameter for relevance ration and make 3 wrapper methods for "ALWAYS", "MOSTLY" and "MORE OFTEN THAN"
##################################################
def testAllInvariants(my_list, min_nbr_items, abs_threshold=100, rel_threshold = 0):
    list_abs_invariants = []
    list_cpl_invariants = [] #complementary invariants
    for col1 in range(len(my_list[0])): #for each pair of columns                       
        for col2 in range(len(my_list[0])):                        
            if col1 != col2 : # do not compare a column to itself
                name1 = my_list[0][col1]
                name2 = my_list[0][col2]
                if not("=" in name1 and "=" in name2 and name1.split('=')[0] == name2.split('=')[0]) : # do not compare categorical columns (those having an equality sign) if they have the same prefix                    
                        for pred2 in [True, False]:#not negating the first variable, only the second one
                            INV = Invariant(my_list, name1, name2, True, pred2)  
                            INV_CPL = Invariant(my_list, name1, name2, False, pred2)
                            if NEGATE_CATEGORICAL_VARIABLES or pred2 or (name2 not in all_categ_columns): #do not continue if pred2 is False and this is a categorical variable that should not be negated                                                               
                                relevance_ratio = INV.getPercentage()/INV_CPL.getPercentage() if INV_CPL.getPercentage() != 0 else 999999                                
                                if INV.getPercentage() >= abs_threshold and INV.getNbrOfAttestations() >= min_nbr_items and relevance_ratio >= rel_threshold:                                     
                                    list_abs_invariants.append(INV)                                    
                                    list_cpl_invariants.append(INV_CPL)
    return (list_abs_invariants, list_cpl_invariants)
 
##################################################                              
#Prints the absolute invariants each one on a separate line  
##################################################    
def printAbsoluteInvariantsLong(list_abs_invariants):
    print("Absolute invariants")
    print("===================")
    i=1
    for INV in list_abs_invariants:
        print(str(i), ". ", end='', sep='')                        
        print(INV.getMathView())
        #print(INV.getEnglishView() + " (" + INV.getPercentageAndFraction() + ")")
        print()
        i = i+1

def printAbsoluteInvariantsConcised(list_abs_invariants, mathView=False):
    printThresholdInvariantsConcised(list_abs_invariants, 100, mathView)

def printNonAbsoluteInvariantsConcised(list_abs_invariants, abs_threshold, mathView=False):
    printThresholdInvariantsConcised(list_abs_invariants, abs_threshold, mathView)    

# MathView: True if we want to print in Math view, False if we want English view
def printThresholdInvariantsConcised(list_abs_invariants, abs_threshold, mathView=False):
    if abs_threshold == 100:
        print("Absolute invariants")
        print("===================")
    else:
        print("Invariants with at least", abs_threshold, "%")
        print("=============================")
    
    i=1
    j=0    
    while j < len(list_abs_invariants):        
        INV1 = list_abs_invariants[j]    
        string = str(i) + ". "
        #print(str(i), ". ", end='', sep='')                                        
        if not mathView:
            if abs_threshold == 100:
                #print("ALL ", end="")
                string += "ALL "
            else:
                string += "MOST "
            
        if mathView:
            #print(INV1.get_header_left(), "=> ", end="")
            string += INV1.get_header_left() +  "=> "
        else:
            #print(INV1.getLeftEnglish(), " ", sep="", end="")
            string += INV1.getLeftEnglish() + " "
        lengthPart1 = len(string) 
        emptyPrefix = " " * lengthPart1
        if mathView:
            #print(INV1.get_header_right(), " [", INV1.getFraction() if threshold == 100 else INV1.getPercentageAndFraction(), "]", sep="", end="")    
            string += INV1.get_header_right() + " [" + (INV1.getFraction() if abs_threshold == 100 else INV1.getPercentageAndFraction()) + "]"
        else:
            #print(INV1.getRightEnglish(), " [", INV1.getFraction() if threshold == 100 else INV1.getPercentageAndFraction(), "]", sep="", end="")    
            string += INV1.getRightEnglish() + " [" + (INV1.getFraction() if abs_threshold == 100 else INV1.getPercentageAndFraction()) + "]"        
        INV2 = INV1             
        j = j+1        
        if j < len(list_abs_invariants) :
            string += ","
        print(string)
        while j < len(list_abs_invariants) and INV1.get_header_left() == list_abs_invariants[j].get_header_left():            
            string = emptyPrefix
            INV2 = list_abs_invariants[j]
            if mathView:
                #print(", ", INV2.get_header_right(), " [", INV2.getFraction() if threshold == 100 else INV2.getPercentageAndFraction(), "]", sep="", end="")    
                string += INV2.get_header_right() + " [" + (INV2.getFraction() if abs_threshold == 100 else INV2.getPercentageAndFraction()) + "]"
            else:
                #print(", ", INV2.getRightEnglish(), " [", INV2.getFraction() if threshold == 100 else INV2.getPercentageAndFraction(), "]", sep="", end="")        
                string += INV2.getRightEnglish() + " [" + (INV2.getFraction() if abs_threshold == 100 else INV2.getPercentageAndFraction()) + "]"
            j = j+1      
            if j < len(list_abs_invariants) :
                string += ","
            print(string)
        print()
        i = i+1
            
def printMoreOftenInvariantsConcised(list_abs_invariants,list_cpl_invariants, rel_threshold=0):
    title = "\"More often\" invariants, relative threshold: " + str(rel_threshold)
    print(title)
    print(len(title)*"=")
    
    i=1
    j=0    
    while j < len(list_abs_invariants):        
        INV1 = list_abs_invariants[j]    
        INV_CPL1 = list_cpl_invariants[j]    
        string = str(i) + ". "            
        string += INV1.getLeftEnglish() + " MORE OFTEN "
        lengthPart1 = len(string) 
        emptyPrefix = " " * lengthPart1
        
        #print(INV1.getRightEnglish(), " [", INV1.getFraction() if threshold == 100 else INV1.getPercentageAndFraction(), "]", sep="", end="")    
        #string += INV1.getRightEnglish() + " [" + INV1.getPercentageAndFraction() + "]" + " THAN " + INV_CPL1.getLeftEnglish() + " [" + INV_CPL1.getPercentageAndFraction() + "]"
        string += INV1.getRightEnglish() + " [" + INV1.getPercentageAndFraction() + "]" + " THAN " + "other artifacts" + " [" + INV_CPL1.getPercentageAndFraction() + "]"
        
        INV2 = INV1
        j = j+1        
        if j < len(list_abs_invariants) :
            string += ","
        print(string)
        while j < len(list_abs_invariants) and INV1.get_header_left() == list_abs_invariants[j].get_header_left():            
            string = emptyPrefix
            INV2 = list_abs_invariants[j]
            INV_CPL2 = list_cpl_invariants[j]        
            #print("TEST: INV_CP2: ", INV_CPL2.getEnglishView() , " " ,INV_CPL2.countLeftIsTrue, INV_CPL2.aANDb )
        
            #string += INV2.getRightEnglish() + " [" + INV2.getPercentageAndFraction() + "]" " THAN " + INV_CPL2.getLeftEnglish() + " [" + INV_CPL2.getPercentageAndFraction() + "]"
            string += INV2.getRightEnglish() + " [" + INV2.getPercentageAndFraction() + "]" " THAN " + "other artifacts" + " [" + INV_CPL2.getPercentageAndFraction() + "]"

            j = j+1      
            if j < len(list_abs_invariants) :
                string += ","
            print(string)
        print()
        i = i+1 

def printInvariantResult(inv, perc, i, dic):
    if(inv != ""):
        if(perc == 100): #absolute invariant get printed first
            print(str(i), ". ", end='', sep='')
            i+=1
            print(inv)
            #print()
        else:
            if perc in dic:
                dic[perc].append(inv)
            else:
                dic[perc]=[inv]
    return i

#def draw_abs_unvariants(single_var=None):    
#    G = nx.DiGraph()    
#
#    #remove unnecessqry invariants if single_var is enabled
#    if single_var != None:
#        to_delete=[]    
#        for k,v in abs_invariants.items():
#            if get_var_name(k) != single_var: 
#                to_delete.append(k)                 
#        for k in to_delete:
#            del abs_invariants[k]
#    
#        #print("absolute invariants after deletions:\n", abs_invariants)
#    
#    nodes = np.arange(0, len(abs_invariants_cols)).tolist()
#    #print("nodes=", nodes)    
#    G.add_nodes_from(nodes)          
#                
#    for k,v in abs_invariants.items():    
#        for col2 in v:
#            if single_var==None or get_var_name(k)==single_var or get_var_name(col2)==single_var:
#                G.add_edge(abs_invariants_cols.index(k), abs_invariants_cols.index(col2), weight=3, color='b')
#    labels={}
#    for i in range(len(abs_invariants_cols)):
#        labels[i] = abs_invariants_cols[i] 
#    
#    ll = [n for n in G if G.degree(n) == 0]
#    #print(ll)
#    for n in ll:
#        G.remove_node(n)
#        del labels[n]
#    left_nodes=[]
#    for i in labels:
#        if get_var_name(labels[i])==single_var:
#            left_nodes.append(i)
#
#    pos=nx.bipartite_layout(G, left_nodes)         
#    weights = nx.get_edge_attributes(G,'weight').values()    
#    
#    plt.figure(figsize=(20,12))    
#    nx.draw_networkx(G, pos=pos, labels = labels, width=list(weights), 
#                     bbox = dict(facecolor = "skyblue",
#                     boxstyle = "round", ec = "silver", pad = 0.3),
#                     edge_color = "black", arrowsize=20
#                     )
#    plt.margins(x=0.4) 
#    plt.savefig("image.png", dpi=300)
#    plt.show()
    
###############################################################################
# Draw all absolute invariants as a bipartite graph (with repetitions of nodes)
# First parameter: a list of Invariant objects
# Second parameter: if different than None, gives the list of variables that 
# need to be drawn on the left side of the bipartite graph.
###############################################################################
def draw_abs_unvariants_bip(list_abs_invariants, left_nodes=None):    
    left_nodes_labels = []
    right_nodes_labels = []
    for inv in list_abs_invariants:
        if left_nodes == None or (inv.getCol1() in left_nodes):
            if inv.get_header_left() not in left_nodes_labels:
                left_nodes_labels.append(inv.get_header_left())
            if inv.get_header_right() not in right_nodes_labels:
                right_nodes_labels.append(inv.get_header_right())    
    all_nodes_labels = {}
    for i in range(len(left_nodes_labels)):
        all_nodes_labels[i] = left_nodes_labels[i]
    for i in range(len(right_nodes_labels)):
        all_nodes_labels[len(left_nodes_labels)+i] = right_nodes_labels[i]
    
    left_nodes_labels + right_nodes_labels
    left_nodes_indexes = [i for i in range(len(left_nodes_labels))]
    all_nodes_indexes = [i for i in range(len(all_nodes_labels))]
    
    G = nx.DiGraph()    
    G.add_nodes_from(all_nodes_indexes)    

    for inv in list_abs_invariants: # add all edges
        if left_nodes == None or inv.getCol1() in left_nodes:
            edge_origin = left_nodes_labels.index(inv.get_header_left())
            edge_destination = len(left_nodes_labels) + right_nodes_labels.index(inv.get_header_right())
            G.add_edge(edge_origin, edge_destination, weight=2, color='b')

    pos=nx.bipartite_layout(G, left_nodes_indexes )         
    weights = nx.get_edge_attributes(G,'weight').values()    
    
    plt.figure(figsize=(20,12))    
    nx.draw_networkx(G, pos=pos, labels = all_nodes_labels, width=list(weights), 
                     bbox = dict(facecolor = "skyblue",
                     boxstyle = "round", ec = "silver", pad = 0.3),
                     edge_color = "black", arrowsize=20
                     )
    plt.margins(x=0.2) 
    plt.savefig("image-bip.png", dpi=300)
    plt.show()
        
def get_var_name(x):
    if "=" in x: #categorical variable
        return x.split("=")[0]
    else:
        if "NOT(" in x:
            return x[4:-1]
        else:
            return x

###############################################################################        
# Returns the value of the column name as a string
# Ex: for "DividerType=Lotus-bud", returns "Lotus-bud"
# Used mostly for categorical variables, but can be used for boolean variables,
#in which case it returns "True" or "False" (as strings)
###############################################################################
def get_var_value(x):
    if "=" in x: # categorical variable
        return x.split("=")[1]
    else: # boolean value
        if "NOT(" in x:
            return "False"
        else:
            return "True"
        
def oppose(name1, name2=""):
    new_list = prepare_data(INPUT_FILE, INPUT_FILE_ALL_BOOLS)  
    contrast(new_list, "contrast-table-"+name1+"_"+name2, name1, name2)
    

def contrast(my_list, filename, name1, name2=""):
    rowList=[]
    found = False
    row1 = []
    row2 = []
    rowNames = [name1]
    if(name2 == ""):
        rowNames.append("NOT("+ name1+ ")")
    else:
        rowNames.append(name2)
    colNames = []
    for col2 in range(len(my_list[0])):                        
        right = my_list[0][col2]        
        rightVar = right.split('=')[0]
        name1Var = name1.split('=')[0]
        name2Var = name2.split('=')[0]
        
        if name1Var != rightVar and name2Var != rightVar: # do not compare categorical columns (those having an equality sign) if they have the same prefix                                                    
            
            INV1 = Invariant(my_list, name1, right, True, True)  
            if name2 == "":
                INV2 = Invariant(my_list, name1, right, False, True)                
            else:
                INV2 = Invariant(my_list, name2, right, True, True)    
            #if right=="Divider":
            #    print("-----------",right, ": ", INV1.frequencyLabel(), " (", INV1.getPercentageAndFraction() ,   ") vs ", INV2.frequencyLabel(), " (", INV2.getPercentageAndFraction(), ")", sep="")
            if INV1.contrastsTo(INV2): 
                #if self.getCol2()=="Divider":
                #print("-----",right)
                #print( INV1.countLeftIsTrue != 0 and INV2.countLeftIsTrue != 0)
                colNames.append(right)
                if not found:
                    found=True
                    if(name2 != ""):
                        spaces = len(name1+" contrasts with "+name2)
                        print(name1+" contrasts with "+name2, end="")
                    else:
                        spaces = len(name1+" contrasts with NOT("+ name1+ ")")
                        print(name1+" contrasts with NOT(", name1, ")", end="")
                else:
                    #spaces = len(name1+" contrasts with ")
                    for i in range(spaces):
                        print(" ",end="")
                if(name2 != ""):                
                    print(" on ", right, ": ", INV1.frequencyLabel(), " (", INV1.getPercentageAndFraction() ,   ") vs ", INV2.frequencyLabel(), " (", INV2.getPercentageAndFraction(), ")", sep="")
                else:
                    print(" on ", right, ": ", INV1.frequencyLabel(), " (", INV1.getPercentageAndFraction(),   ") vs ", INV2.frequencyLabel(), " (", INV2.getPercentageAndFraction(), ")", sep="")
                row1.append(INV1.frequencyLabel() + " (" + str(INV1.getPercentage()) + "%)" + "  ["+ str(INV1.getFraction())+"]")
                row2.append(INV2.frequencyLabel() + " (" + str(INV2.getPercentage()) + "%)" + "  ["+ str(INV2.getFraction())+"]")                        
                rowList.append([INV1.frequencyLabel() + " (" + str(INV1.getPercentage()) + "%)" + "  ["+ str(INV1.getFraction())+"]", INV2.frequencyLabel() + " (" + str(INV2.getPercentage()) + "%)" + "  ["+ str(INV2.getFraction())+"]"])

    if not found:
        print("No opposed variables found")
    else:
            
        fig, ax = plt.subplots(dpi=300)    
        # hide axes
        fig.patch.set_visible(False)
        ax.axis('off')
        ax.axis('tight')
        # ax.table(cellText=[row1, row2],
        #                   rowLabels=rowNames,
        #                   colLabels=colNames,
        #                   cellLoc="center",
        #                   loc="top")

        ax.table(cellText=rowList,
                          rowLabels=colNames,
                          colLabels=rowNames,
                          cellLoc="center",
                          loc="bottom")
        #fig.tight_layout()
        #plt.savefig(filename+".pdf")
        plt.savefig(filename+".png", dpi=300)
        plt.show()
        
    
##Draw a graph focusing on one specific column
#def draw_bipartite(col_name):
#     G = nx.DiGraph()
#    nodes = np.arange(0, len(abs_invariants_cols)).tolist()
#    print("nodes=", nodes)
#    G.add_nodes_from(nodes)
#    for k,v in abs_invariants.items():
#        for col2 in v:
#            G.add_edge(abs_invariants_cols.index(k), abs_invariants_cols.index(col2), weight=3, color='b')
#    labels={}
#    for i in range(len(abs_invariants_cols)):
#        labels[i] = abs_invariants_cols[i] 
#    print("labels=", labels)
#    pos=nx.shell_layout(G)
#    
#    #plt.title("Organogram of a company.")
#    #plt.savefig("Output/plain organogram using networkx.jpeg", dpi = 300)
#    plt.figure(figsize=(20,12))
#    
#    #nx.draw_networkx(G, pos = pos, labels = labels, arrows = True, node_shape = "s", node_color = "white",
##                     node_size=100,font_size=12)
#    weights = nx.get_edge_attributes(G,'weight').values()
#    colors = nx.get_edge_attributes(G,'color').values()
#    
#    nx.draw_networkx(G, pos=pos, labels = labels, width=list(weights), 
#                     bbox = dict(facecolor = "skyblue",
#                     boxstyle = "round", ec = "silver", pad = 0.3),
#                     edge_color = "black", arrowsize=20
#                     )
#    plt.margins(x=0.4) 
#    plt.savefig("image.png")
#    plt.show()
#    
    
############################################################
# Main function, that launches the complete analysis.
############################################################
def analyze(inputFileName, outputFileName):
    print_headers()    
    new_list = prepare_data(inputFileName, outputFileName)    
    
    #testAll(new_list) #old version
    
    # Absolute invariants
    list_inv = findAllAbsoluteInvariants(new_list, MIN_NBR_ITEMS)#testAllInvariants(new_list, min_nbr_items=MIN_NBR_ITEMS)     
    printAbsoluteInvariantsConcised(list_inv)     
    #draw_abs_unvariants_bip(list_inv, ["Polity"])
    print()
 
    # Non-absolute Invariants
    list_inv = findAllNonAbsoluteInvariants(new_list, MIN_NBR_ITEMS, ABS_THRESHOLD) #testAllInvariants(new_list, MIN_NBR_ITEMS, ABS_THRESHOLD)
    printNonAbsoluteInvariantsConcised(list_inv, ABS_THRESHOLD)
    #draw_abs_unvariants_bip(list_inv, ["Polity"])
    
    #Invariants of type "more often than"
    list_inv, list_cpl_inv = findAllMoreOftenThanInvariants(new_list, MIN_NBR_ITEMS, RELATIVE_THRESHOLD)#testAllInvariants(new_list, MIN_NBR_ITEMS, 0, RELATIVE_THRESHOLD)
    printMoreOftenInvariantsConcised(list_inv, list_cpl_inv, rel_threshold=RELATIVE_THRESHOLD)
    #draw_abs_unvariants_bip(list_inv, ["Polity"])
    #TODO: make a graphical representation of these invariants (same graph as before?)

    #contrast(new_list, "Iconic", "Iconic")    
    contrast(new_list, "Israel-Judah", "Polity=Israel", "Polity=Judah")
    #contrast(new_list, "test-handle", "Attestation=Handle")
    #contrast(new_list, "Jerusalem-Judah", "Provenance=Jerusalem")


################################################                       
################ MAIN ##########################                       
################################################
analyze(INPUT_FILE, INPUT_FILE_ALL_BOOLS)                
################################################
