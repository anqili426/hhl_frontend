import csv
import os
import statistics
import sys
from pathlib import Path

def process_data(data_dict):
    dict = {
        "forall": {},
        "exists": {},
        "forall-exists": {},
        "exists-forall": {}
    }

    for key, value in data_dict.items():
        keyStrings = key.split("/")
        type = keyStrings[3]    # The type of the hyperproperty
        source = keyStrings[4]  # The source of the benchmark
        source_dict = dict.get(type)
        if source in source_dict:
            source_dict[source].append(value)
        else:
            source_dict[source]=[value]

    resDir = Path("result")
    if not resDir.exists():
        resDir.mkdir(parents=True, exist_ok=True)
    with open("result/result.csv", 'w', newline='') as file:
        writer = csv.writer(file)
        for type, source_dict in dict.items():
            writer.writerow(["Type of hyperproperties: " + type])
            writer.writerow(["Source", "No. of benchmarks", "Mean runtime(s)", "Median runtime(s)"])
            all_runtimes_per_type = []
            for source, runtimes in source_dict.items():
                runtime_mean_per_type_per_source = statistics.mean(runtimes) if len(runtimes) > 0 else 0
                runtime_median_per_type_per_source = statistics.median(runtimes) if len(runtimes) > 0 else 0
                all_runtimes_per_type.extend(runtimes)
                writer.writerow([source, str(len(runtimes)), str(runtime_mean_per_type_per_source), str(runtime_median_per_type_per_source)])
            runtime_mean_per_type = statistics.mean(all_runtimes_per_type) if len(all_runtimes_per_type) > 0 else 0
            runtime_median_per_type = statistics.median(all_runtimes_per_type) if len(all_runtimes_per_type) > 0 else 0
            writer.writerow(["Overall", str(len(all_runtimes_per_type)), str(runtime_mean_per_type), str(runtime_median_per_type)])
            writer.writerow([])
    
def calculate_average(csv_folder):
    # Dictionary to store data for each row
    data_dict = {}

    try:
        # Loop through each CSV file in the folder
        for filename in os.listdir(csv_folder):
            if filename.endswith(".csv"):
                with open(os.path.join(csv_folder, filename), 'r') as file:
                    reader = csv.reader(file)
                    # Skip header
                    next(reader)
                    for row in reader:
                        key = row[0]
                        value = float(row[2])
                        # Check if the key already exists in the dictionary
                        if key in data_dict:
                            data_dict[key].append(value)
                        else:
                            data_dict[key] = [value]
    except FileNotFoundError:
        print("Error: the directory " + csv_folder + " does not exist")
        sys.exit(1)
        
    # Calculate the average for each key
    average_dict = {}
    for key, values in data_dict.items():
        average_dict[key] = statistics.mean(values)
    return average_dict

def write_output(average_dict, output_filename):
    # Write the output to a new CSV file
    with open(output_filename, 'w', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(['First Column', 'Average of Third Column'])
        for key, value in average_dict.items():
            writer.writerow([key, value])

if __name__ == "__main__":
    if len(sys.argv) <= 1:
        print("Please specify the directory in which the runtime data is located")
    else:
        csv_folder = sys.argv[1]
        average_dict = calculate_average(csv_folder)
        print(average_dict)
        process_data(average_dict)
