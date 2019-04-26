
# import all functions from the tkinter 
from tkinter import *
# importing required libraries 
import requests, json 

# Create a GUI window 
root = Tk() 

# create a global variables 
variable1 = StringVar(root) 
variable2 = StringVar(root) 

# initialise the variables 
variable1.set("currency") 
variable2.set("currency") 

	
# Function to perform real time conversion 
# from one currency to another currency 
#def RealTimeCurrencyConversion(): 
#    # currency code 
#    from_currency = variable1.get() 
#    to_currency = variable2.get() 
#    
#    # enter your api key here 
#    api_key = "Your_Api_Key"
#    
#    # base_url variable store base url 
#    base_url = r"https://www.alphavantage.co/query?function = CURRENCY_EXCHANGE_RATE"
#    
#    # main_url variable store complete url 
#    main_url = base_url + "&from_currency =" + from_currency + "&to_currency =" + to_currency + "&apikey =" + api_key 
#    
#    # get method of requests module 
#    # return response object 
#    req_ob = requests.get(main_url) 
#    
#    # json method return json format 
#    # data into python dictionary data type. 
#    
#    # result contains list of nested dictionaries 
#    result = req_ob.json() 
#    
#    # parsing the required information 
#    Exchange_Rate = float(result["Realtime Currency Exchange Rate"] 
#    										['5. Exchange Rate']) 
#    
#    # get method of Entry widget 
#    # returns current text as a 
#    # string from text entry box. 
#    amount = float(CritNet_field.get()) 
#    
#    # calculation for the conversion 
#    new_amount = round(amount * Exchange_Rate, 3) 
#    
#    # insert method inserting the 
#    # value in the text entry box. 
#    ShieldNet_field.insert(0, str(new_amount)) 


# Function for clearing the Entry field 
def generate_const_json(): 
    constraints ={}
    constraints["critical_nets"] = CritNet_field.get().strip().split()
    constraints["shielded_nets"] = ShieldNet_field.get().strip().split()
    constraints["matching_blocks"]  =[]
    for blocks in MatchBlock_field.get().strip().split(';'):
        if blocks.strip():
            [block1,block2] = blocks.strip().split()
            match= {"block1":block1, "block2":block2}
            constraints["matching_blocks"].append(match)
    constraints["Symmetrical_nets"] = []
    for nets in SymmNet_field.get().strip().split(';'):
        if nets.strip():
            [net1, net2] = nets.strip().split(',')
            print(net1,net2)
            net1=net1.strip().split()
            net2=net2.strip().split()
            match= {"net1":net1[0], "net2":net2[0], "pins1":net1[1:-1] , "pins2":net2[1:-1]}
            constraints["matching_blocks"].append(match)
    
    with open('constraint.json', 'w') as outfile:
        json.dump(constraints, outfile)
    #CritNet_field.delete(0, END) 
    #ShieldNet_field.delete(0, END)
#def read_const_text():

# Driver code 
if __name__ == "__main__" : 
    """ 
    example inputs:
    Critical Nets: n1 n2
    Shield Nets: n1 n2 n3
    Match blocks: b1 b2; b3 b4
    Symmetrical nets: n1 p1 p2, n2 p22 p21; n2 p1,n3 p3
    """
    menu = Menu(root) 
    root.config(menu=menu) 
    filemenu = Menu(menu) 
    menu.add_cascade(label='File', menu=filemenu) 
    filemenu.add_command(label='New') 
    filemenu.add_command(label='Open...') 
    filemenu.add_separator() 
    filemenu.add_command(label='Exit', command=root.quit) 
    helpmenu = Menu(menu) 
    menu.add_cascade(label='Help', menu=helpmenu) 
    helpmenu.add_command(label='About')

    # Set the background colour of GUI window 
    root.configure(background = 'white') 
    
    # Set the configuration of GUI window (WidthxHeight) 
    root.geometry("600x400") 
    
    # Create welcome to Real Time Currency Convertor label 
    headlabel = Label(root, text = ' Welcome to constraint writer package', 
    				fg = 'black', bg = "cyan") 
    
    label1 = Label(root, text = "Critical Nets :", fg = 'black', bg = 'white') 
    label2 = Label(root, text = "Shielded Nets(GND) :", fg = 'black', bg = 'white') 
    label3 = Label(root, text = "Match Blocks \n(; seperated pairs):", fg = 'black', bg = 'white') 
    label4 = Label(root, text = "Symmetrical Nets(pin list) : \ne.g neta pin1 pin2, netb pinq pinr; ", fg = 'black', bg = 'white') 
    
    # grid method is used for placing the widgets at respective positions in table like structure . 
    headlabel.grid(row = 0, column = 1) 
    label1.grid(row = 2, column = 0) 
    label2.grid(row = 4, column = 0) 
    label3.grid(row = 6, column = 0) 
    label4.grid(row = 8, column = 0) 
    
    # Create a text entry box 
    # for filling or typing the information. 
    CritNet_field = Entry(root) 
    ShieldNet_field = Entry(root) 
    MatchBlock_field = Entry(root) 
    SymmNet_field = Entry(root) 
    
    # ipadx keyword argument set width of entry space. 
    CritNet_field.grid(row = 2, column = 1, ipadx ="25") 
    ShieldNet_field.grid(row = 4, column = 1, ipadx ="25") 
    MatchBlock_field.grid(row = 6, column = 1, ipadx ="25") 
    SymmNet_field.grid(row = 8, column = 1, ipadx ="25") 
    
    # list of currency codes 
    #shild_options = ["VDD","VSS"] 
    
    # create a drop down menu using OptionMenu function 
    # which takes window name, variable and choices as 
    # an argument. use * befor the name of the list, 
    # to unpack the values 
    #shield_option = OptionMenu(root, shield_type, *) 
    #ToCurrency_option = OptionMenu(root, variable2, *CurrenyCode_list) 
    
    #FromCurrency_option.grid(row = 2, column = 1, ipadx = 10) 
    #ToCurrency_option.grid(row = 3, column = 1, ipadx = 10) 
    
    # Create a Convert Button and attached 
    # with RealTimeCurrencyExchangeRate function 
    #button1 = Button(root, text = "Convert", bg = "red", fg = "black", 
    #							command = RealTimeCurrencyConversion) 
    #
    #button1.grid(row = 4, column = 1) 
    
    # Create a Clear Button and attached 
    # with delete function 
    #button1 = Button(root, text = "Read constraint from text", bg = "cyan", 
    #				fg = "black", command = read_const_text) 
    #button1.grid(row = 10, column = 0) 
    button2 = Button(root, text = "Generate constraint json", bg = "green", 
    				fg = "black", command = generate_const_json) 
    button2.grid(row = 10, column = 1) 
    
    # Start the GUI 
    root.mainloop() 
