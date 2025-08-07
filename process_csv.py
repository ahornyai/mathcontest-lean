problems = open("problems.csv").readlines()
out = open("out.csv", "w")

lines_out = [problems[0]]

for problem in problems[1:]:
    name, solved, topics = problem.split(",", 2)
    
    # setup markdown link
    if name.startswith("Arany"):
        name = f"[{name}](Arany/{name}.lean)"
    elif name.startswith("OKTV"):
        name = f"[{name}](OKTV/{name}.lean)"
    
    if solved == "Y":
        solved = "✅"
    elif solved == "N":
        solved = "❌"
    
    lines_out.append(",".join([name, solved, topics]))

out.writelines(lines_out)