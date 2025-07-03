import matplotlib.pyplot as plt
import re

def extract_hex_values(filename):
    """
    Extract the last hex values from each line in the file.
    Expected format: #MDS*[hex_string];([numbers],hex_value)
    """
    hex_values = []
    decimal_values = []
    
    try:
        with open(filename, 'r') as file:
            for line_num, line in enumerate(file, 1):
                line = line.strip()
                if not line:
                    continue
                
                # Use regex to find the last hex value in parentheses
                # Pattern matches: ([anything],hex_value)
                pattern = r'\([^,]+,[^,]+,[^,]+,([0-9A-Fa-f]+)\)'
                match = re.search(pattern, line)
                
                if match:
                    hex_val = match.group(1)
                    hex_values.append(hex_val)
                    
                    # Convert hex to decimal for plotting
                    try:
                        decimal_val = int(hex_val, 16)
                        decimal_values.append(decimal_val)
                    except ValueError:
                        print(f"Warning: Could not convert hex value '{hex_val}' on line {line_num}")
                        decimal_values.append(0)
                else:
                    print(f"Warning: No hex value found on line {line_num}: {line[:50]}...")
    
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        return [], []
    except Exception as e:
        print(f"Error reading file: {e}")
        return [], []
    
    return hex_values, decimal_values

def plot_hex_values(filename):
    """
    Plot the hex values from the file.
    """
    hex_values, decimal_values = extract_hex_values(filename)
    
    if not decimal_values:
        print("No hex values found to plot.")
        return
    
    # Create the plot
    plt.figure(figsize=(12, 8))
    
    # Plot the decimal values
    plt.plot(decimal_values, 'b-', linewidth=1, alpha=0.7)
    plt.scatter(range(len(decimal_values)), decimal_values, c='red', s=10, alpha=0.6)
    plt.title(f'Hex Values from {filename}')
    plt.xlabel('Line Number')
    plt.ylabel('Decimal Value')
    plt.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.show()
    
    # Print some statistics
    print(f"\nStatistics:")
    print(f"Total values: {len(decimal_values)}")
    print(f"Min value: {min(decimal_values)} (0x{min(decimal_values):X})")
    print(f"Max value: {max(decimal_values)} (0x{max(decimal_values):X})")
    print(f"Average: {sum(decimal_values)/len(decimal_values):.2f}")
    
    # Show first few and last few hex values
    print(f"\nFirst 5 hex values: {hex_values[:5]}")
    print(f"Last 5 hex values: {hex_values[-5:]}")

def main():
    # You can change this filename to your input file
    filename = "data.txt"  # Change this to your file path
    
    print(f"Processing file: {filename}")
    plot_hex_values(filename)

if __name__ == "__main__":
    main()