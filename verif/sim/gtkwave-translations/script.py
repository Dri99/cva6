i=0
with open("verif/sim/gtkwave-translations/fu_op","r") as f:
     line=f.readline()
     while line:
             print("{:08b}".format(i) + line,end="")
             i=i+1
             line=f.readline()