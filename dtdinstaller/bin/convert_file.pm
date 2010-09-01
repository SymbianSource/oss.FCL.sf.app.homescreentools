#
# Copyright (c) 2007 Nokia Corporation and/or its subsidiary(-ies).
# All rights reserved.
# This component and the accompanying materials are made available
# under the terms of "Eclipse Public License v1.0"
# which accompanies this distribution, and is available
# at the URL "http://www.eclipse.org/legal/epl-v10.html".
#
# Initial Contributors:
# Nokia Corporation - initial contribution.
#
# Contributors:
#
# Description:  
#
package Convert_file;

# Hash of file meta information (name etc.).
my %file_meta_info;

# List of logical name entries.
my @entries = ();

sub convert_file {
    my $file_to_process = shift;
    
    %file_meta_info = ();
    @entries = ();
    
    # Convert LOC file to DTD...
    if ($file_to_process =~ /\.loc$/) {
        (my $file_to_write = $file_to_process) =~ s/\.loc$/.dtd/;
        (my $file_log = $file_to_process) =~ s/\.loc$/.log/; 
        &read_loc_file($file_to_process);
        &write_dtd_file($file_to_process, $file_to_write, $file_log);        
    }
    # Convert DTD file to LOC...
    elsif ($file_to_process =~ /\.dtd$/) {
        (my $file_to_write = $file_to_process) =~ s/\.dtd$/.loc/;
        (my $file_log = $file_to_process) =~ s/\.dtd$/.log/; 
        &read_dtd_file($file_to_process);
        &write_loc_file($file_to_process, $file_to_write, $file_log);        
    }
    else {
        print "Unknown file format.\n";
    }
}

# This subroutine reads DTD file into a data structure. Reading is done line
# by line.
# Adding extra complexity to this subroutine is the fact that ENTITY tag can
# either be declared before attribute definitions or after them.
sub read_dtd_file { 
    my $file_to_process = shift;
    
    open(FILE, $file_to_process) 
    or die "Can't open `$file_to_process' for reading: $!";
    
    my %entry;
    my $attribute_read = "FALSE";
    my $entity_read = "FALSE";    
    
    while (my $line = <FILE>) {
        # NCR notation is used in DTD files. This is removed since it's not
        # used in LOC files.
        #&remove_NCR_notation(\$line);
        chomp($line);
        
        SWITCH: {            
            # Extract file meta data. 
            # Matches eg. <FileName: "<name_of_dtd_file>">
            if ($line =~ /\s*(<FileName|<PartOf|<FileDescription|<FileVersion)\s*:\s*".[^"]*/) {
                (my $item_name, my $content) = 
                                       $line =~ /\s*<(.[^\s]*)\s*:\s*"(.[^"]*)/;                
                $file_meta_info{$item_name} = $content;
                last SWITCH;
            }
            # Matches ENTITY tag eg. 
            # <!ENTITY <logical_name> "<engineering_english_string>">
            if ($line =~ /\s*<!ENTITY\s*.[^\s]*\s*".[^"]*/) 
            {   
                # Case entity -> attributes -> entity
                if ($attribute_read eq "TRUE" && $entity_read eq "TRUE") {
                    my %temp = %entry;
                    %entry = ();
                    push @entries, \%temp;                
                    $attribute_read = "FALSE";
                    $entity_read = "TRUE";                    
                
                    (my $loc_name, my $translation) = 
                                $line =~ /\s*<!ENTITY\s*(.[^\s]*)\s*"(.[^"]*)/;
                
                     $entry{'logical_name'} = $loc_name;
                     $entry{'translation'} = $translation;                     
                }
                # Case attributes -> entity
                elsif ($attribute_read eq "TRUE" && $entity_read eq "FALSE") {                                   
                    (my $loc_name, my $translation) = 
                                $line =~ /\s*<!ENTITY\s*(.[^\s]*)\s*"(.[^"]*)/;
                
                     $entry{'logical_name'} = $loc_name;
                     $entry{'translation'} = $translation;
                     
                     my %temp = %entry;
                     %entry = ();
                     push @entries, \%temp;                
                     $attribute_read = "FALSE";
                     $entity_read = "FALSE"; 
                }
                # Case: nothing has been read yet.
                elsif ($attribute_read eq "FALSE" && $entity_read eq "FALSE") {
                    (my $loc_name, my $translation) = 
                                $line =~ /\s*<!ENTITY\s*(.[^\s]*)\s*"(.[^"]*)/;
                
                     $entry{'logical_name'} = $loc_name;
                     $entry{'translation'} = $translation;
                     $entity_read = "TRUE"; 
                }
                
                last SWITCH;
            }
            # Matches attributes e.g.
            # <logical_name>.layout "<layout>"            
            if ($line =~ /\s*.[^\.]*(.layout|.description|.recycled|.release|.grammar|.term|.refers|.islocalizable|.item_type|.action_before|.action_after|.variables|.parents)\s*".[^"]*/) {
                (my $item_name, my $content) = 
                                $line =~ /\s*.[^\.]*.(.[^\s]*)\s*"(.[^"]*)/;
                                
                $item_name =~ s/parents/Parents/;
                $item_name =~ s/variables/Variables/;
                
                $entry{$item_name} = $content;
                last SWITCH;
            }
            # Matches attribute tag.
            if ($line =~ /\s*.[^\.]*.attributes/) {
                # Case: entity -> attributes -> attributes
                if ($entity_read eq "TRUE" && $attribute_read eq "TRUE") {
                    my %temp = %entry;
                    %entry = ();
                    push @entries, \%temp;
                    $entity_read = "FALSE";                    
                }   
                $attribute_read = "TRUE";
                
                last SWITCH;
            }
        }
    }

    # Include last entry also to results. This happens if file ends with an
    # entry where attributes are defined after ENTITY.
    if ($attribute_read eq "TRUE" && $entity_read eq "TRUE") {        
        my %temp = %entry;
        %entry = ();
        push @entries, \%temp;
    }
    
    close FILE;
}

# This subroutine reads LOC file into a data structure. Reading is done line
# by line.
sub read_loc_file {    
    my $file_to_process = shift;
    
    chmod ($file_to_process, 0777); # Make sure that file can be read, before trying to open it
    
    open(FILE, $file_to_process) 
    or die "Can't open `$file_to_process' for reading: $!";
    
    my %entry;
        
    while (my $line = <FILE>) {
        # NCR notation is used in DTD files. Not allowed characters are
        # converted to NCR.
        #&add_NCR_notation(\$line);
        chomp($line);
        
        # Each line with #define defines a logical name/translation pair. This
        # is saved to the data structure.
        if ($line =~ /\s*#define\s*.[^\s]*\s*".[^"]*/) {
                (my $item_name, my $content) = 
                                  $line =~ /\s*#define\s*(.[^\s]*)\s*"(.*)"$/;                
                    
                $entry{'logical_name'} = $item_name;
                $entry{'translation'} = $content;
                my %temp = %entry;
                %entry = ();
                push @entries, \%temp;
        }                
    }    
    
    close FILE;
}

# This subroutine writes the data into a LOC file.
sub write_loc_file {  
    my $file_to_process = shift;
    my $file_to_write = shift;
    my $file_log = shift;
    
    open(my $file_handle, ">$file_to_write") 
    or die "Can't open `$file_to_write' for writing: $!";
        
    open(my $log_file_handle, ">$file_log") 
    or die "Can't open `$file_log' for writing: $!";
    
    my $tstamp = localtime(time);  
    
    print $log_file_handle "Log created $tstamp:\n" . 
                           "Errors and warnings for conversion of " .
                           "$file_to_process to $file_to_write\n\n";
    
    # Write file header info. Mostly static text.
    &write_loc_header($file_handle);
    
    print $file_handle "\n";
    
    # This array defines the order in which attributes are written to a LOC
    # file.
    my @fields = ("item_type", "action_before", "action_after", "grammar", 
               "refers", "Parents", "Variables");
    
    for my $i (0 .. $#entries) {
        # Analyze entry for correctness and report possible errors.
        &print_dtd_errors_and_warnings(\%{$entries[$i]}, $log_file_handle);
        
        # Seach for attributes and write them to output if found.
        for my $y (0 .. $#fields) {
            if (exists($entries[$i]{$fields[$y]})) {
                print $file_handle 
                         "//d: [$fields[$y]] : \"$entries[$i]{$fields[$y]}\"\n";
            }
        }   
        
        print $file_handle "//d: $entries[$i]{'description'}\n";
        print $file_handle "//l: $entries[$i]{'layout'}\n";
        print $file_handle "//r: $entries[$i]{'release'}\n";
            
        print $file_handle "#define $entries[$i]{'logical_name'}" . 
                           " \"$entries[$i]{'translation'}\"\n\n";        
    }
    
    close $file_handle;
    close $log_file_handle;
}

sub print_dtd_errors_and_warnings {
    my $entry_ref = shift;
    my $log_file_handle = shift;    
    
    # Either description or item_type and action_before should be defined.
    if (!exists($entry_ref->{'description'}) && 
       !(exists($entry_ref->{'item_type'}) && 
        exists($entry_ref->{'action_before'})))
    {
        print $log_file_handle "ERROR: $entry_ref->{'logical_name'} " .
                               "does not have any description data!\n";
    }
    if (!exists($entry_ref->{'layout'})) {
        print $log_file_handle "ERROR: $entry_ref->{'logical_name'} " .
                               "missing layout definition!\n";
    }
    if (!exists($entry_ref->{'release'})) {
        print $log_file_handle "ERROR: $entry_ref->{'logical_name'} " .
                               "missing release information!\n";
    }
    if (!exists($entry_ref->{'Parents'})) {
        print $log_file_handle "ERROR: $entry_ref->{'logical_name'} " .
                               "missing parent reference!\n";
    }
    # Grammar should be defined if translation is a single word.
    if (!($entry_ref->{'translation'} =~ /\s/) && 
        !exists($entry_ref->{'grammar'})) {
        print $log_file_handle "\tWARNING: $entry_ref->{'logical_name'} " .
                               "is a single word, but no grammar data is " .
                               "given!\n";
    }
    # Variables should be defined if translation contains variables.
    if ($entry_ref->{'translation'} =~ /\%/ &&
        !exists($entry_ref->{'Variables'})) {
        print $log_file_handle "\tWARNING: $entry_ref->{'logical_name'} " .
                               "has a variable or parameter, but no variable " .
                               "data is given!\n";
    }    
}

# This subroutine writes the data into a DTD file. Only ENTITY definitions are 
# written i.e. no attribute definitions.
sub write_dtd_file {
    my $file_to_process = shift;
    my $file_to_write = shift;
    my $file_log = shift;
    
    open(my $file_handle, ">$file_to_write") 
    or die "Can't open `$file_to_write' for writing: $!";
    
    open(my $log_file_handle, ">$file_log") 
    or die "Can't open `$file_log' for writing: $!";
    
    my $tstamp = localtime(time);  
    
    print $log_file_handle "Log created $tstamp:\n" . 
                           "Errors and warnings for conversion of " .
                           "$file_to_process to $file_to_write\n\n";
    
    # Write file header info. Mostly static text.
    my $file_name = "";    
    if ($file_to_process =~ /\//) {
        ($file_name) = $file_to_process =~ /\/(.[^\/]*)$/;
    }
    else {
        $file_name = $file_to_process;
    }    
    &write_dtd_header($file_handle, $file_name);
    
    for my $i (0 .. $#entries) {
        print $log_file_handle "Found $entries[$i]{'logical_name'}\n";
        
        $entries[$i]{'translation'} =~ s/\\"/&quot;/g;
        
        print $file_handle "<!ENTITY $entries[$i]{'logical_name'}" . 
                           " \"$entries[$i]{'translation'}\">\n";        
    }

    close $file_handle;
    close $log_file_handle;    
}

sub write_loc_header {
    my $file_handle = shift;
    print $file_handle <<EOT;
CHARACTER_SET UTF8
// This file is best viewed with a non-proportian font, such as Courier
// Or copied into a spreadsheet application.
/*
* ============================================================================
* Name        :  $file_meta_info{'FileName'}
* Part Of     :  $file_meta_info{'PartOf'}
* Version     :  $file_meta_info{'FileVersion'}
* 
* Description :  $file_meta_info{'FileDescription'}
* 
* Copyright © 2005 Nokia Corporation. This material, including
* documentation and any related computer programs, is protected by
* copyright controlled by Nokia Corporation. All rights are reserved.
* Copying, including reproducing, storing, adapting or translating, any
* or all of this material requires the prior written consent of Nokia
* Corporation. This material also contains confidential information
* which may not be disclosed to others without the prior written consent
* of Nokia Corporation.
* ============================================================================
*/
EOT
}

sub write_dtd_header {  
    my $file_handle = shift;
    my $file_to_process = shift;
    
    my $tstamp = localtime(time);    
    
    print $file_handle <<EOT;
<?xml version="1.0" encoding="UTF-8"?>
<!-- 
DTD file generated from $file_to_process
$tstamp 
by LocDTDConverter
-->
EOT
}

# Subroutine to add NCR notation to string.
sub add_NCR_notation {
    my $string = shift;
    # Replace characters with NCR notation. 'eh' is used to denote &# character
    # sequence. If this is not used then &# sequence would be also replaced with
    # NCR.
    $$string =~ s/'/eh39;/g;
    $$string =~ s/\%/eh37;/g;    
    $$string =~ s/>/eh62;/g;
    $$string =~ s/</eh60;/g;
    $$string =~ s/&/eh38;/g;
    
    $$string =~ s/eh(\d{2});/&#$1;/g;    
}

# Subroutine to remove NCR notation from a string.
sub remove_NCR_notation {
    my $string = shift;
    
    $$string =~ s/&#39;/'/g;    
    $$string =~ s/&#37\;/\%/g;
    $$string =~ s/&#38;/&/g;
    $$string =~ s/&#62;/>/g;
    $$string =~ s/&#60;/</g;
}

1;
