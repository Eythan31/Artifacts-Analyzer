import os, sys
import csv
#from PyQt5.QtCore import pyqtSlot
from PyQt5.QtWidgets import QMainWindow, QDialog, QTableWidgetItem, QFileDialog
from PyQt5 import QtWidgets
from PyQt5.uic import loadUi
#import matplotlib.pyplot as plt

########################################
## PARAMETERS (TO BE SET BY THE USER) ##
########################################
INPUT_FILE = "seals-ABRIDGED-2023-07-31.csv"#"seals-ABRIDGED-2023-07-31.csv"

ABS_THRESHOLD_DEFAULT = 75
ABS_THRESHOLD = ABS_THRESHOLD_DEFAULT

RELATIVE_THRESHOLD_DEFAULT = 2 #Relevance ratio for invariants
RELATIVE_THRESHOLD = RELATIVE_THRESHOLD_DEFAULT #Relevance ratio for invariants

MIN_NBR_ITEMS_DEFAULT = 4
MIN_NBR_ITEMS = MIN_NBR_ITEMS_DEFAULT

CSV_DELIMITER_DEFAULT = ","
CSV_DELIMITER = CSV_DELIMITER_DEFAULT

REMOVE_FIRST_COLUMN_DEFAULT = True #in case the first column contains an identifier which should not be used in the search for invariants (otherwise, use False)
REMOVE_FIRST_COLUMN = REMOVE_FIRST_COLUMN_DEFAULT #in case the first column contains an identifier which should not be used in the search for invariants (otherwise, use False)

NEGATE_CATEGORICAL_VARIABLES_DEFAULT = False #should categorical variables be negated as well or only boolean variables
NEGATE_CATEGORICAL_VARIABLES = NEGATE_CATEGORICAL_VARIABLES_DEFAULT  #should categorical variables be negated as well or only boolean variables

DO_NOT_NEGATE_FIRST_VARIABLE_DEFAULT = True #do not search for invariants of the shape NOT(A) => B and NOT(A) => NOT(B)
DO_NOT_NEGATE_FIRST_VARIABLE = DO_NOT_NEGATE_FIRST_VARIABLE_DEFAULT #do not search for invariants of the shape NOT(A) => B and NOT(A) => NOT(B)

#Contrasts:
CONTRAST_BY_RATIO_DEFAULT = False
CONTRAST_BY_RATIO = CONTRAST_BY_RATIO_DEFAULT

RELATIVE_THRESHOLD_CONTRASTS_DEFAULT = 1.5 #Relevance ratio for contrasts
RELATIVE_THRESHOLD_CONTRASTS = RELATIVE_THRESHOLD_CONTRASTS_DEFAULT #Relevance ratio for contrasts

CONTRAST_BY_SKIPPING_DEFAULT = True
CONTRAST_BY_SKIPPING = CONTRAST_BY_SKIPPING_DEFAULT

CONTRASTS_SKIPPED_CLASSES_DEFAULT = 1 # Minimum number of classes to be skipped to be considered as a contrast (0 if none to be skipped)
CONTRASTS_SKIPPED_CLASSES = CONTRASTS_SKIPPED_CLASSES_DEFAULT # Minimum number of classes to be skipped to be considered as a contrast (0 if none to be skipped)

CONTRAST_BY_GAP_DEFAULT = False # Do we want sliding contrast gaps?
CONTRAST_BY_GAP = CONTRAST_BY_GAP_DEFAULT # Do we want sliding contrast gaps?

SLIDING_CONTRASTS_GAP = 25 #Sliding contrasts gap, in percents
SLIDING_CONTRASTS_GAP_DEFAULT = SLIDING_CONTRASTS_GAP #Sliding contrasts gap, in percents

#CONTRAST_THRESHOLD = 75 # threshold for contrasting invariants (for the "MOSTLY/USUALLY" category)
#CONTRAST_THRESHOLD = 75 # threshold for contrasting invariants (for the "MOSTLY/USUALLY" category)

MIN_NBR_ITEMS_CONTRASTS_DEFAULT = 5 #minimun nbr of items for inclusion in contrast table when one of the invariants as 0 occurrences
MIN_NBR_ITEMS_CONTRASTS = MIN_NBR_ITEMS_CONTRASTS_DEFAULT #minimun nbr of items for inclusion in contrast table when one of the invariants as 0 occurrences

########################################
INPUT_FILE_ALL_BOOLS = "input-all-booleans.csv"
GEOGRAPHICAL_KEYWORDS = ["polity", "city", "country", "region", "provenance", "land"]
ADJECTIVES = ["iconic", "pierced", "perforated", "divided", "bordered", "painted", "colored", "coloured", "burnished"]
########################################


###########################
all_boolean_columns = []
all_categ_columns = []
abs_invariants = {}
abs_invariants_cols = []
########################################

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
def resource_path(relative_path):
  if hasattr(sys, '_MEIPASS'):
      return os.path.join(sys._MEIPASS, relative_path)
  return os.path.join(os.path.abspath('.'), relative_path)

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
        
# def findAllAbsoluteInvariants(my_list, min_nbr_items):
#     invs, invs_cpl = testAllInvariants(my_list, min_nbr_items)     
#     return invs

# def findAllNonAbsoluteInvariants(my_list, min_nbr_items, abs_threshold):
#     invs, invs_cpl = testAllInvariants(my_list, min_nbr_items, abs_threshold)
#     return invs

# #returns a list of invariants and a list of complementary invariants (A=>B and NOT(A)=>B)
# def findAllMoreOftenThanInvariants(my_list, min_nbr_items, rel_threshold):
#     return testAllInvariants(my_list, min_nbr_items, 0, rel_threshold)

##################################################
# Find all invariants (helper function for the above 3 functions)
# Parameter: boolean matrix
# Returns a list of Invqriqnt objects  
# Add parameter for relevance ration and make 3 wrapper methods for "ALWAYS", "MOSTLY" and "MORE OFTEN THAN"
##################################################
# def testAllInvariants(my_list, min_nbr_items, abs_threshold=100, rel_threshold = 0):
#     list_abs_invariants = []
#     list_cpl_invariants = [] #complementary invariants
#     for col1 in range(len(my_list[0])): #for each pair of columns                       
#         for col2 in range(len(my_list[0])):                        
#             if col1 != col2 : # do not compare a column to itself
#                 name1 = my_list[0][col1]
#                 name2 = my_list[0][col2]
#                 if not("=" in name1 and "=" in name2 and name1.split('=')[0] == name2.split('=')[0]) : # do not compare categorical columns (those having an equality sign) if they have the same prefix                    
#                         for pred2 in [True, False]:#not negating the first variable, only the second one
#                             INV = Invariant(my_list, name1, name2, True, pred2)  
#                             INV_CPL = Invariant(my_list, name1, name2, False, pred2)
#                             if NEGATE_CATEGORICAL_VARIABLES or pred2 or (name2 not in all_categ_columns): #do not continue if pred2 is False and this is a categorical variable that should not be negated                                                               
#                                 relevance_ratio = INV.getPercentage()/INV_CPL.getPercentage() if INV_CPL.getPercentage() != 0 else 999999                                
#                                 if INV.getPercentage() >= abs_threshold and INV.getNbrOfAttestations() >= min_nbr_items and relevance_ratio >= rel_threshold:                                     
#                                     list_abs_invariants.append(INV)                                    
#                                     list_cpl_invariants.append(INV_CPL)
#     return (list_abs_invariants, list_cpl_invariants)

def applyPredicate(boolean, predicate) :
     if predicate:
         return boolean
     else:
         return not boolean
    
def printAbsoluteInvariantsConcised(list_abs_invariants, mathView=False):
    return printThresholdInvariantsConcised(list_abs_invariants, 100, mathView)

def printNonAbsoluteInvariantsConcised(list_abs_invariants, abs_threshold, mathView=False):
    return printThresholdInvariantsConcised(list_abs_invariants, abs_threshold, mathView)    

# MathView: True if we want to print in Math view, False if we want English view
def printThresholdInvariantsConcised(list_abs_invariants, abs_threshold, mathView=False):
    # if abs_threshold == 100:
    #     print("Absolute invariants")
    #     print("===================")
    # else:
    #     print("Invariants with at least", abs_threshold, "%")
    #     print("=============================")
    
    i=1
    j=0 
    full_string = ""
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
        #print(string)
        full_string += string
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
            #print(string)
            full_string += "\n"
            full_string += string
            
        #print("\n")
        full_string += "\n"
        full_string += "\n"
        i = i+1
    return full_string

######################################
def printMoreOftenInvariantsConcised(list_abs_invariants,list_cpl_invariants, rel_threshold=0):
    # title = "\"More often\" invariants, relative threshold: " + str(rel_threshold)
    # print(title)
    # print(len(title)*"=")
    
    i=1
    j=0    
    full_string = ""

    while j < len(list_abs_invariants):        
        #print("in big loop, j=", j)
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
        #print(string)
        full_string += string
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
            #print(string)
            full_string += "\n"
            full_string += string
        #print()
        full_string += "\n"
        full_string += "\n"
        i = i+1 
    return full_string

############################
def contrast(my_list, filename, name1, name2=""):
    rowList=[]
    found = False
    row1 = []
    row2 = []
    rowNames = [name1]
    full_string = ""
    matrix = []
    if(name2 == ""):
        rowNames.append("NOT("+ name1+ ")")
    else:
        rowNames.append(name2)
    colNames = []
    for col2 in range(len(my_list[0])):                        
        row = []
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
                        full_string += (name1+" contrasts with "+name2)
                    else:
                        spaces = len(name1+" contrasts with NOT("+ name1+ ")")
                        print(name1+" contrasts with NOT(", name1, ")", end="")
                        full_string += (name1+" contrasts with NOT("+ name1+ ")")
                else:
                    #spaces = len(name1+" contrasts with ")
                    for i in range(spaces):
                        print(" ",end="")
                        full_string += " "
                row.append(right)
                if(name2 != ""):                
                    print(" on ", right, ": ", INV1.frequencyLabel(), " (", INV1.getPercentageAndFraction() ,   ") vs ", INV2.frequencyLabel(), " (", INV2.getPercentageAndFraction(), ")", sep="")
                    full_string += " on " + right + ": " + INV1.frequencyLabel() + " (" + INV1.getPercentageAndFraction() +   ") vs " + INV2.frequencyLabel() + " (" + INV2.getPercentageAndFraction() + ")\n"
                    row.append(INV1.frequencyLabel() + " (" + str(INV1.getPercentage()) + "%)" + "  ["+ str(INV1.getFraction())+"]")
                    row.append(INV2.frequencyLabel() + " (" + str(INV2.getPercentage()) + "%)" + "  ["+ str(INV2.getFraction())+"]")
                else:
                    print(" on ", right, ": ", INV1.frequencyLabel(), " (", INV1.getPercentageAndFraction(),   ") vs ", INV2.frequencyLabel(), " (", INV2.getPercentageAndFraction(), ")", sep="")
                    full_string += " on " + right + ": " + INV1.frequencyLabel() + " (" + INV1.getPercentageAndFraction() +  ") vs " + INV2.frequencyLabel() + " (" + INV2.getPercentageAndFraction() + ")\n"
                    row.append(INV1.frequencyLabel() + " (" + str(INV1.getPercentage()) + "%)" + "  ["+ str(INV1.getFraction())+"]")
                    row.append(INV2.frequencyLabel() + " (" + str(INV2.getPercentage()) + "%)" + "  ["+ str(INV2.getFraction())+"]")
                row1.append(INV1.frequencyLabel() + " (" + str(INV1.getPercentage()) + "%)" + "  ["+ str(INV1.getFraction())+"]")
                row2.append(INV2.frequencyLabel() + " (" + str(INV2.getPercentage()) + "%)" + "  ["+ str(INV2.getFraction())+"]")                        
                rowList.append([INV1.frequencyLabel() + " (" + str(INV1.getPercentage()) + "%)" + "  ["+ str(INV1.getFraction())+"]", INV2.frequencyLabel() + " (" + str(INV2.getPercentage()) + "%)" + "  ["+ str(INV2.getFraction())+"]"])
                matrix.append(row)

    if not found:
        print("No opposed variables found")
        full_string += "No opposed variables found"
    return full_string, matrix

###########################################################
############## SETTINGS DIALOG CLASS ######################
###########################################################
class SettingsDialog(QDialog):
    def __init__(self):
       super(SettingsDialog, self).__init__()
       loadUi(resource_path("./Settings-dialog.ui"), self)
       self.setDefaultSettings()
       self.buttonBox.accepted.connect(self.updateSettings)
       
    def setDefaultSettings(self):
        self.abs_threshold_input.setText(str(ABS_THRESHOLD))
        self.rel_threshold_input.setText(str(RELATIVE_THRESHOLD))
        self.min_nbr_input.setText(str(MIN_NBR_ITEMS))
        self.csv_delimiter_input.setText(CSV_DELIMITER)
        if REMOVE_FIRST_COLUMN:
            self.remove_first_column_input.setChecked(True) 
        if NEGATE_CATEGORICAL_VARIABLES:
            self.negate_categ_vars_input.setChecked(True) 
        if DO_NOT_NEGATE_FIRST_VARIABLE:
            self.do_not_negate_first_var_input.setChecked(True) 
        if CONTRAST_BY_RATIO:
            self.contrast_by_ratio_input.setChecked(True) 
        self.rel_threshold_contrasts_input.setText(str(RELATIVE_THRESHOLD_CONTRASTS))
        if CONTRAST_BY_SKIPPING:
            self.contrast_by_skip_input.setChecked(True) 
        self.contrast_skipped_classes.setValue(CONTRASTS_SKIPPED_CLASSES)
        if CONTRAST_BY_GAP:
            self.contrast_by_gap_input.setChecked(True) 
        self.sliding_contrasts_gap_input.setText(str(SLIDING_CONTRASTS_GAP))
        
    def updateSettings(self):
        global ABS_THRESHOLD, RELATIVE_THRESHOLD, MIN_NBR_ITEMS, CSV_DELIMITER,\
            REMOVE_FIRST_COLUMN, NEGATE_CATEGORICAL_VARIABLES,\
            DO_NOT_NEGATE_FIRST_VARIABLE, CONTRAST_BY_RATIO,\
            RELATIVE_THRESHOLD_CONTRASTS, CONTRAST_BY_SKIPPING,\
            CONTRASTS_SKIPPED_CLASSES, CONTRAST_BY_GAP, SLIDING_CONTRASTS_GAP
            
        ABS_THRESHOLD = int(self.abs_threshold_input.text())
        RELATIVE_THRESHOLD = float(self.rel_threshold_input.text())
        MIN_NBR_ITEMS = int(self.min_nbr_input.text())
        CSV_DELIMITER = self.csv_delimiter_input.text()
        REMOVE_FIRST_COLUMN = self.remove_first_column_input.isChecked()
        NEGATE_CATEGORICAL_VARIABLES = self.negate_categ_vars_input.isChecked()
        DO_NOT_NEGATE_FIRST_VARIABLE = self.do_not_negate_first_var_input.isChecked()
        CONTRAST_BY_RATIO =  self.contrast_by_ratio_input.isChecked()
        RELATIVE_THRESHOLD_CONTRASTS =  float(self.rel_threshold_contrasts_input.text())
        CONTRAST_BY_SKIPPING =  self.contrast_by_skip_input.isChecked()
        CONTRASTS_SKIPPED_CLASSES = self.contrast_skipped_classes.value()
        CONTRAST_BY_GAP = self.contrast_by_gap_input.isChecked()
        SLIDING_CONTRASTS_GAP = int(self.sliding_contrasts_gap_input.text())
        if mainWindow.file_opened :
            mainWindow.compute_all()
        
###########################################################
############## MAIN WINDOW CLASS ##########################
###########################################################

    
class Window1(QMainWindow):
    def __init__(self):
       super(Window1, self).__init__()
       #loadUi(resource_path("./Artifacts-analyzer.ui"), self)
       if getattr(sys, 'frozen', False):
            RELATIVE_PATH = os.path.dirname(sys.executable)
       else:
            RELATIVE_PATH = os.path.dirname(__file__)
       self._ui_path = RELATIVE_PATH #+ "/ui_path"  # Update this as needed                
       loadUi(os.path.join(self._ui_path, 'Artifacts-analyzer.ui'), self)
       
       self.file_opened  = False
        # Open action
       self.actionOpen.triggered.connect(self.open_clicked)       
       self.contrastButton.clicked.connect(self.launch_contrast)
       self.actionSettings.triggered.connect(self.settings_clicked)
        
    def open_clicked(self):
        self.file_opened = True
        options = QFileDialog.Options()
        options |= QFileDialog.DontUseNativeDialog
        fileName, _ = QFileDialog.getOpenFileName(self,"QFileDialog.getOpenFileName()", "","CSV Files (*.csv)", options=options)
        if fileName:
            print("Opening file" + fileName)
        
        self.new_list = prepare_data(fileName, "test-output.csv")
        self.compute_all()
        
    
    def compute_all(self):
        # Absolute Invariants
        list_inv = findAllAbsoluteInvariants(self.new_list, MIN_NBR_ITEMS)#testAllInvariants(new_list, min_nbr_items=MIN_NBR_ITEMS)     
        self.textEdit_all.setHtml("<pre>"+printAbsoluteInvariantsConcised(list_inv) + "</pre>")
                
        # Non-absolute Invariants
        list_inv = findAllNonAbsoluteInvariants(self.new_list, MIN_NBR_ITEMS, ABS_THRESHOLD) #testAllInvariants(new_list, MIN_NBR_ITEMS, ABS_THRESHOLD)
        self.textEdit_most.setHtml("<pre>"+ printNonAbsoluteInvariantsConcised(list_inv, ABS_THRESHOLD) + "</pre>")

        #Invariants of type "more often than"
        list_inv, list_cpl_inv = findAllMoreOftenThanInvariants(self.new_list, MIN_NBR_ITEMS, RELATIVE_THRESHOLD)#testAllInvariants(new_list, MIN_NBR_ITEMS, 0, RELATIVE_THRESHOLD)
        self.textEdit_more_often.setHtml("<pre>"+ printMoreOftenInvariantsConcised(list_inv, list_cpl_inv, rel_threshold=RELATIVE_THRESHOLD) + "</pre>")
        
        #Contrast
        self.comboBox_contrast_1.clear()
        self.comboBox_contrast_2.clear()
        self.comboBox_contrast_1.addItems(self.new_list[0])        
        self.comboBox_contrast_2.addItems([""] + self.new_list[0])
        self.contrastTableWidget.clear()
    
    def launch_contrast(self):
        if self.comboBox_contrast_2.currentText() != "":
            contrast_result, matrix = contrast(self.new_list, "temp-contrast", self.comboBox_contrast_1.currentText(), self.comboBox_contrast_2.currentText())
        else:
            contrast_result, matrix = contrast(self.new_list, "temp-contrast", self.comboBox_contrast_1.currentText())
        #self.textEdit_contrast.setHtml("<pre>"+ contrast_result + "</pre>")
        self.contrastTableWidget.setColumnCount(3)
        self.contrastTableWidget.setRowCount(len(matrix))
        if self.comboBox_contrast_2.currentText()=="":
            self.contrastTableWidget.setHorizontalHeaderLabels(["", self.comboBox_contrast_1.currentText(), "Others"])
        else:
            self.contrastTableWidget.setHorizontalHeaderLabels(["", self.comboBox_contrast_1.currentText(), self.comboBox_contrast_2.currentText()])
        self.contrastTableWidget.horizontalHeader().setStyleSheet( "QHeaderView::section { border-bottom: 1px solid gray; }" );
        #self.contrastTableWidget.insertRow(1)
        for i in range(0, len(matrix)):
            for j in range(0,3):
                self.contrastTableWidget.setItem(i,j, QTableWidgetItem(matrix[i][j]))
        self.contrastTableWidget.resizeColumnsToContents()
        if len(matrix) == 0:
            QtWidgets.QMessageBox.information(self, 'Message', 'There are no contrasting variables.', QtWidgets.QMessageBox.Ok)        
            
    def settings_clicked(self):
        self.settingsDialog = SettingsDialog()
        self.settingsDialog.show()
        
        
app = QtWidgets.QApplication(sys.argv)
mainWindow = Window1()
mainWindow.show()
app.exec_()
   