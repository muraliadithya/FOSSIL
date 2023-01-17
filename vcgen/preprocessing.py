def remove_comments(user_input):
    '''Remove comments in the input file.
    Comments opened by /* and closed by */
    The user_input is a list of lines read from a file.

    Nested comments are allowed.
    Code followed by a comment in the same line is allowed.
    Code to the right of a comment in a line is not allowed.
    '''
    for i in range(len(user_input)):
        user_input[i] = user_input[i].strip()
    comment_nesting = 0
    updated_input = []
    for line in user_input:
        if len(line) == 0:
            pass
        elif comment_nesting == 0:
            contains_comment = 0
            latest_noncomment_index = -1
            j = 0
            comment_ended = 0
            while j < len(line)-1:
                if (comment_ended == 1) and (not (line[j].isspace())) and (not (line[j:j+2] == '/*')):  #a non-comment starts after a line with a comment
                    raise Exception('Code to the right of a comment is not allowed')
                if line[j:j+2] == '/*':
                    comment_nesting = comment_nesting + 1
                    if latest_noncomment_index == -1:
                        contains_comment = 1
                        latest_noncomment_index = j
                    j = j+2
                elif line[j:j+2] == '*/':
                    comment_nesting = comment_nesting - 1
                    if comment_nesting < 0:
                        raise Exception ('Unpaired comment end */')
                    if comment_nesting == 0:
                        comment_ended = 1
                    j = j+2
                else:
                    j = j+1
            if contains_comment == 0:
                updated_input.append(line)
            elif latest_noncomment_index == 0:
                pass
            else:
                updated_input.append(line[:latest_noncomment_index])

        else:
            if len(line)>1:
                j = 0
                comment_ended = 0
                while j < len(line)-1:
                    if (comment_ended == 1) and (not (line[j].isspace())) and (not (line[j:j+2] == '/*')):  #a non-comment starts after a line with a comment
                        raise Exception('Code to the right of a comment is not allowed')
                    if line[j:j+2] == '/*':
                        comment_nesting = comment_nesting + 1
                        j = j+2
                    elif line[j:j+2] == '*/':
                        comment_nesting = comment_nesting - 1
                        if comment_nesting < 0:
                            raise Exception ('Unpaired comment end */')
                        if comment_nesting == 0:
                            comment_ended = 1
                        j = j+2
                    else:
                        j = j+1
    if comment_nesting != 0:
        raise Exception ('Unpaired comments')
    return updated_input


def ml_to_sl(user_input):
    '''
    user_input is a list of lines read from a file. There are no comments in this file.
    This converts codes in multiple lines into a single line'''
    updated_input = []
    current_formula = ''
    parantheses_nesting = 0
    for line in user_input:
        if parantheses_nesting == 0:
            current_formula = line
        elif parantheses_nesting > 0:                       #may just use >=0 with a single if statement
            current_formula = current_formula + ' ' + line
        for elt in line:
            if elt == '(':
                parantheses_nesting = parantheses_nesting+1
            elif elt == ')':
                parantheses_nesting = parantheses_nesting-1
                if parantheses_nesting < 0:
                    raise Exception('(Parts of) Two inputs in same line')

        if parantheses_nesting == 0:
            updated_input.append(current_formula)
            current_formula = ''
    if parantheses_nesting != 0:
        raise Exception ('Incomplete Parantheses')
    return updated_input

def listify(input_string):
    '''input_string is a single complete line of code. No comments. 
    
    Converts into a nested list based on paranthesis.
    '''
    sofar=[]
    parenthesis_pairs= []
    parantheses_nesting = 0
    parenthesis_found = 0
    for i,elt in enumerate(input_string):
        if elt=='(' :
            parantheses_nesting = parantheses_nesting+1
            if parenthesis_found == 0:
                parenthesis_found = 1
                open_paranthesis_index = i
        if elt==')':
            parantheses_nesting = parantheses_nesting-1
            if parantheses_nesting < 0:
                raise Exception('Unpaired closing paranthesis )')
        if parenthesis_found == 1:
            if parantheses_nesting == 0:
                #found '(' and its corresponding ')'
                close_parenthesis_index = i
                parenthesis_pairs.append((open_paranthesis_index,close_parenthesis_index))
                parenthesis_found = 0 #move on
    if len(parenthesis_pairs) == 0:
        sofar.append(input_string)
        return sofar
    first = input_string[:(parenthesis_pairs[0][0])]
    last = input_string[(parenthesis_pairs[-1][1])+1:]
    if len(first)==0:
        pass
    else:
        if (not (first.isspace())):
            sofar.append(first)
    for i in range(len(parenthesis_pairs)-1):
        open_paranthesis_index,close_parenthesis_index = parenthesis_pairs[i][0], parenthesis_pairs[i][1]
        z = parenthesis_pairs[i+1][0]

        sofar.append(listify(input_string[open_paranthesis_index+1:close_parenthesis_index]))
        now = input_string[close_parenthesis_index+1:z]
        if len(now)==0:
            pass
        else:
            if (not (now.isspace())):
                sofar.append(now)
    secondlast = input_string[parenthesis_pairs[-1][0]+1:parenthesis_pairs[-1][1]]
    sofar.append(listify(secondlast))
    if len(last)==0:
        pass
    else:
        if (not (last.isspace())):
            sofar.append(last)
    return sofar


def make_list(semip_list): #elements can be strings or lists
    '''lisftify doesn't take stuff like 'list x' and give ['list', 'x]. It keeps it as ['list x'].
       make_list takes care of this. Assuming the input is given correctly, everytime a space is
       followed by something, it is safe to split'''
    def string_to_list(strng):
        l = []
        if len(strng)<= 1: #must be non empty if input is correct
            if len(strng) == 0 or strng.isspace():
                return l
            l.append(strng)
            return l
        i = 0
        while i<len(strng):
            if (not (strng[i].isspace())):
                if i==0 or strng[i-1].isspace():
                    for j in range(i,len(strng)):
                        if j==len(strng)-1 or strng[j+1].isspace():
                            l.append(strng[i:j+1])
                            i=j+2
                            break
            else:
                i=i+1
        return l

    newlist = []


    for i in semip_list:
        if isinstance(i,str):
            x = string_to_list(i)
            for j in x:
                newlist.append(j)
        else:
            newlist.append(make_list(i))
    return newlist


def create_input(input_string):
    ''''Take a use given input and convert it into the input format used by the vc method '''
    return make_list(listify(input_string))[0]


# To complete preprocessing, read the text file-> remove comments -> multiline to singleline -> create input for each element in the resulting list. 