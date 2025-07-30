import os
import sys

def parse_graph(file):
    """
    Parses a graph description file and constructs a nested dictionary representing the graph.
    The input file is expected to contain lines describing edges in the following format:
        source->target [label="label_value", style="", color="color_value"]
    Returns a dictionary where each source node maps to another dictionary. This inner dictionary
    maps a key of the form "label_color" to a list of target nodes connected by edges with the
    specified label and color.
    Args:
        file (str): Path to the graph description file.
    Returns:
        dict: Nested dictionary representing the graph structure.
    """
    graph_dict = {}
    with open(file, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if "->" in line:
                parts = line.split("->") # S02->S03 [label="complete", style="", color="blue"]
                source = parts[0]
                target = parts[1].split(" ")[0]
                label = parts[1].split("label=")[1].split(',')[0].replace('"', '')
                color = parts[1].split("color=")[1].split(']')[0].replace('"', '')

                key = f"{label}_{color}"
                if source not in graph_dict:
                    graph_dict[source] = {}
                if key not in graph_dict[source]:
                    graph_dict[source][key] = []
                graph_dict[source][key].append(target)

    return graph_dict

def get_data(graph_dict):
    """
    Analyzes a graph dictionary to extract statistics about states, transitions, and functions.
    Args:
        graph_dict (dict): A dictionary representing a graph, where each key is a source state,
            and each value is a dictionary mapping transition labels (in the form 'label_color')
            to lists of target states.
    Returns:
        tuple: A tuple containing the following statistics:
            - int: Number of unique states (excluding one, possibly the initial state).
            - int: Number of unique function labels.
            - int: Total number of transitions.
            - int: Number of transitions with color 'black'.
            - int: Number of transitions with color 'blue'.
            - int: Number of 'blue' transitions excluding those with label 't' or 'constructor'.
            - int: Number of transitions with colors other than 'black' or 'blue'.
            - int: Number of transitions with colors other than 'black' or 'blue',
            excluding those with label 't' or 'constructor'.
    """
    estados = set()
    funciones_set = set()
    transiciones_totales = 0
    transiciones_black = 0
    transiciones_blue = 0
    transiciones_blue_sin_time = 0
    transiciones_hm = 0
    transiciones_hm_sin_time = 0

    for source, transitions in graph_dict.items():
        estados.add(source)
        for key, targets in transitions.items():
            estados.update(targets)
            label, color = key.split('_')
            transiciones_totales += len(targets)
            funciones_set.add(label)
            if color == 'black':
                transiciones_black += len(targets)
            elif color == 'blue':
                transiciones_blue += len(targets)
                if label != "t" and label != "constructor":
                    transiciones_blue_sin_time += len(targets)
            else:
                transiciones_hm += 1
                if label != "t" and label != "constructor":
                    transiciones_hm_sin_time += 1

    cant_metodos = len(funciones_set)
    return (len(estados)-1, cant_metodos, transiciones_totales, transiciones_black, transiciones_blue, transiciones_blue_sin_time, transiciones_hm, transiciones_hm_sin_time)

def main():
    """
    Main function to generate a formatted table summarizing data extracted from graph files in a specified directory.
    The function expects a single command-line argument specifying the directory path to search for files ending with
    'merge_epa_superblue.dot'. For each matching file, it parses the graph, extracts relevant data, and compiles the
    results into a table with the following columns: Subject, States, |M|, #Trx, #May, #Must, #Must-t, #HM, #HM-t.
    The table is printed to the console with aligned columns and also saved as a tab-separated file named 'table1.txt'.
    Usage:
        python table_1.py <directory_path>
    Args:
        None
    Raises:
        SystemExit: If the number of arguments is incorrect or the provided directory path is invalid.
    """
    if len(sys.argv) != 2:
        print("Usage: python table_1.py <directory_path>")
        print("Example: python table_1.py example/Benchmarks/B1")
        sys.exit(1)

    directory_path = sys.argv[1]

    if not os.path.isdir(directory_path):
        print(f"{directory_path} is not a valid directory.")
        sys.exit(1)

    header = ["Subject", "States", "|M|", "#Trx", "#May", "#Must", "#Must-t", "#HM", "#HM-t"]

    # Collect all rows first to determine max width per column
    rows = []
    rows.append(header)
    for root, _, files in os.walk(directory_path):
        for file in files:
            if file.endswith("merge_epa_superblue.dot"):
                file_path = os.path.join(root, file)
                graph = parse_graph(file_path)
                data = get_data(graph)
                dir_name = root.split(os.path.sep)[-1]
                dir_name = dir_name.replace("_", "\\_")
                row = [dir_name] + [str(x) for x in data]
                rows.append(row)

    # Calculate max width for each column
    col_widths = [max(len(str(row[i])) for row in rows) + 2 for i in range(len(header))]

    # Print header with formatting
    header_fmt = "".join([f"{{:<{w}}}" for w in col_widths])
    print(header_fmt.format(*header))

    output_lines = []
    output_lines.append("\t".join(header))

    # Print and save each row
    for row in rows[1:]:
        print(header_fmt.format(*row))
        output_lines.append("\t".join(row))

    folder_name = os.path.basename(os.path.normpath(directory_path))
    output = f"table_{folder_name}.txt"
    with open(output, "w", encoding="utf-8") as f:
        for line in output_lines:
            f.write(line + "\n")

if __name__ == "__main__":
    main()
