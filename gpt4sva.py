import re, sys
import argparse

def remove_verilog_comments(input_filename, output_filename):
    with open(input_filename, 'r') as infile:
        lines = infile.readlines()

    output_lines = []

    for line in lines:
        # Split the line at the comment symbol (if it exists)
        array = line.split("//")
        if len(array) > 1:
            output_lines.append(array[0] + '\n')
        else:
            output_lines.append(line)

    with open(output_filename, 'w') as outfile:
        outfile.writelines(output_lines)

def remove_multiline_comments_add_header(input_filename, output_filename, header_filename, reg_string, name):
    with open(input_filename, 'r') as infile:
        content = infile.read()

    # Remove multi-line comments
    content_without_comments = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)

    # Load the content from the header file
    with open(header_filename, 'r') as header_file:
        header_content = header_file.read()

    # Swap every instance of '_reg' in header content
    header_content_swapped = header_content.replace('_reg', reg_string)
    header_content_swapped = header_content_swapped.replace('MODULE', name)

    # Combine header and cleaned content
    final_content = header_content_swapped + '\n' + content_without_comments

    # Write the combined content to the output file
    with open(output_filename, 'w') as outfile:
        outfile.write(final_content)

# Assuming the script is executed with the input file's name as a command line argument
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Process verilog files and remove comments.')
    parser.add_argument('f', type=str, help='Name of the input file.')
    parser.add_argument('name', type=str, help='Name of the module.')
    parser.add_argument('-reg', type=str, default='_reg', help='String to swap in header. Default is "_reg".')
    parser.add_argument('-header', type=str, default='SVA_FOOTER.v', help='Path to the header file. Default is "SVA_FOOTER.v".')
    
    args = parser.parse_args()
    
    name = args.name
    input_filename = args.f
    base_filename = input_filename.rsplit('.', 1)[0]  # Removing the extension
    output_filename = "{}_PROMPT.v".format(base_filename)

    remove_verilog_comments(input_filename, output_filename)
    remove_multiline_comments_add_header(output_filename, output_filename, args.header, args.reg, name)
    print("Done! Output written to {}".format(output_filename))