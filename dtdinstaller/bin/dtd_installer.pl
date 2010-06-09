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
# Description:  A tool that install widgets and dtd files.
#  Tool is mainly meant to be used via dtd.mk makefile template,
#  but can be run as such also.
#

use strict;
use FindBin;        # for FindBin::Bin
my $PerlLibPath;    # fully qualified pathname of the directory containing our Perl modules

BEGIN {
# check user has a version of perl that will cope
	require 5.005_03;
# establish the path to the Perl libraries: currently the same directory as this script
	$PerlLibPath = $FindBin::Bin;	# X:/epoc32/tools
# do not convert slashes for linux
	if ($^O eq "MSWin32") {
		$PerlLibPath =~ s/\//\\/g;	# X:\epoc32\tools
		$PerlLibPath .= "\\";
	}
}

use lib $PerlLibPath;

use Cwd;
use Getopt::Long;
use Convert_file; # for .dtd to .loc file conversion
use File::Copy;
use File::Find; # for finding
use File::Path; # mkpath
use File::Basename; # fileparse

if ( $#ARGV < 1)
        {
         print <<USAGE;
Usage: dtd_installer.pl -n dtd_name [-t type][-l dtd_location] [-s sub_folder_name] [-o output_location] [-a action_type] [-f force_create] [-d debug]
 -n: widget or dtd (switch_loc) file name
 -t: optional, default type is dtd and other possibility is widget
 -l: optional, input path location, 
 default for widget type is \\epoc32\\data\\z\\resource\\homescreen
 default for dtd is \\epoc32\\include\\domain\\<layer>\\loc
 -s: optional, for widgets only, default are xuikon and hsps
 -o: optional, default is \\epoc32\\release\\winscw\\udeb\\z\\private\\200159c0\\install
 -a: optional, default is build other possible are what and clean
 -f: optional, for widgets only, themeinstaller is always run for xuikon, even switch loc file don\'t exist
 -d: optional, for debugging purposes (e.g. temporary folders aren't deleted)
 
Example how to run for dtd files only: 
 dtd_installer.pl -n matrixmenudata -o \\epoc32\\data\\z\\private\\200113DD\\content
Example how to run for one widget: 
 dtd_installer.pl -n view -t type widget
Example how to run for all widgets:
 dtd_installer.pl -n all_widgets -t type widget -d yes

USAGE
	exit -1;
	}

my ($dtd_name, $dtd_type, $dtd_location, $sub_folder_name, $output_location, $action_type, $force_create, $debug, $what_output_file);
my (@all_dirs, @find_files, @files_to_convert);
my @sub_folders=("xuikon","hsps");

my $EPOCROOT = $ENV{EPOCROOT};
$EPOCROOT =~ s#[/\\]*$##;

my $PATHSEP='/';
if ($^O eq "MSWin32" ) {
	$PATHSEP='\\';
}

my @layers=(
$EPOCROOT . "${PATHSEP}epoc32${PATHSEP}include${PATHSEP}domain${PATHSEP}osextensions${PATHSEP}loc", 
$EPOCROOT . "${PATHSEP}epoc32${PATHSEP}include${PATHSEP}domain${PATHSEP}middleware${PATHSEP}loc",
$EPOCROOT . "${PATHSEP}epoc32${PATHSEP}include${PATHSEP}domain${PATHSEP}applications${PATHSEP}loc",
$EPOCROOT . "${PATHSEP}epoc32${PATHSEP}include${PATHSEP}platform${PATHSEP}loc",
$EPOCROOT . "${PATHSEP}epoc32${PATHSEP}include${PATHSEP}platform${PATHSEP}mw${PATHSEP}loc",
$EPOCROOT . "${PATHSEP}epoc32${PATHSEP}include${PATHSEP}platform${PATHSEP}app${PATHSEP}loc");

my $themeinstaller_tool = $EPOCROOT  . "${PATHSEP}epoc32${PATHSEP}tools${PATHSEP}themeinstaller${PATHSEP}themeinstaller";
if ($^O eq "MSWin32" ) {
  $themeinstaller_tool = $themeinstaller_tool . ".bat";
}

my $themeinstaller_property_file = $EPOCROOT  . "${PATHSEP}epoc32${PATHSEP}tools${PATHSEP}themeinstaller${PATHSEP}data${PATHSEP}widgetinstaller.prop";

# Set this to 1 if you need to debug the script
# $debug = 1;

GetOptions(
	'n=s' => \$dtd_name,
	't=s' => \$dtd_type,
	'l=s' => \$dtd_location,
	's=s' => \$sub_folder_name,
	'o=s' => \$output_location,
	'a=s' => \$action_type,
	'd=s' => \$debug,
	'f=s' => \$force_create );

check_options();

if (($action_type eq "what") && (-e $what_output_file)) {
	open( WHAT, $what_output_file) or die $!;
	while( <WHAT> ){
		print ;
	}
	close WHAT;
	exit;
} elsif (($action_type eq "clean") && (-e $what_output_file)) {
	unlink $what_output_file;
}

if ($dtd_type eq "widget") {
	if ((lc $dtd_name) eq "all_widgets") {
		# read all widget names from given directory
		opendir(SDIR, $dtd_location) or die("ERROR: dtd_installer.pl, can not open $dtd_location\n");
		@all_dirs = grep !/^\.\.?$/, readdir SDIR;
		closedir(SDIR);
		if (!@all_dirs) {
			warn"ERROR: dtd_installer.pl, couldn't find any widgets:\n";
			die;
		}	
		foreach my $temp_dtd_name (@all_dirs) {
			$dtd_name = $temp_dtd_name;
			my  $dir = "${dtd_location}\\${dtd_name}";
			if (-d $dir) { # Calling process_widget sub routine for every directory
					process_widget();
			}
		}		
	} else { # Only one widget processed
		process_widget();
	}
} else {
	# Run only .loc to .dtd conversion for non widgets
	process_dtd($output_location, $dtd_name);
}

sub process_widget
{
  
  foreach my $sub_f (@sub_folders) {
  	my @lang_dirs;
  	if ($debug) { print "Current subfolder:\n $sub_f\n"; }
  	${sub_folder_name} = $sub_f;
  	if ($debug) { print "Processing widget:\n${dtd_location}\\${dtd_name}\n"; }
  	
  	my $current_time = time;
  	my $full_dtd_input_path = "${dtd_location}\\${dtd_name}\\${sub_folder_name}";
  	my $full_dtd_output_path = "${output_location}\\${dtd_name}\\${sub_folder_name}";
  	my $temp_path = "${dtd_location}\\${dtd_name}\\temp";
  	my $temp_loc_path = "${dtd_location}\\${dtd_name}\\${sub_folder_name}\\temp";
  	my $temp_dtd_path = "${temp_path}\\$current_time";
  	my $temp_loc_files_path = "${temp_loc_path}\\$current_time";
  	my $no_success = 1;
  	my $count = 0;

  	while ($no_success) { # make sure that temporary directory isn't already in the use
  		undef $no_success;
  		$current_time = time;
  		$temp_dtd_path = "${temp_path}\\$current_time";
			mkpath $temp_dtd_path or $no_success=1;
			sleep 1; 
			$count++;
			if ($count > 100 ) { warn: "ERROR: dtd_installer.pl, couldn't create temp directory $temp_dtd_path !!!\nDtd_installer\.pl script stopped\n";	die;}
		}
		$count = 0;
		$no_success = 1;
  	while ($no_success) { # make sure that temporary directory isn't already in the use
  		undef $no_success;
  		$current_time = time;
  		$temp_loc_files_path = "${temp_loc_path}\\$current_time";
			mkpath $temp_loc_files_path or $no_success=1;
			sleep 1; 
			$count++;
			if ($count > 100 ) { warn: "ERROR: dtd_installer.pl, couldn't create temp directory $temp_loc_files_path!!!\nDtd_installer\.pl script stopped\n";	die;}
		}
 	
  	if ($debug) { print "Full dtd input path:\n$full_dtd_input_path\n"; }
  	if ($debug) { print "Full dtd output path:\n$full_dtd_output_path\n"; }
  	opendir(SDIR, $full_dtd_input_path) or die("ERROR: dtd_installer.pl, can not open $full_dtd_input_path\n");
		@lang_dirs = grep !/^\.\.?$/, readdir SDIR;
  	closedir(SDIR);
  	
  	
  	if (${sub_folder_name} eq "xuikon") { # Copy engineering english files always to 00 folder
			copy_files($full_dtd_input_path,"${temp_loc_files_path}\\00");
  	} else{ #hsps folder
  		copy_files($full_dtd_input_path,"${full_dtd_output_path}\\00");
  	}

	
  	foreach my $lang_id (@lang_dirs) {		# generate localized .dtd files

  		my $dtd_temp = "${full_dtd_input_path}\\${lang_id}";
  		if ((-f $dtd_temp) && ($lang_id =~ /.dtd/i) ) { # running loc to dtd for all .dtd files
  				if ($debug) { print "Dtd file found:\n$dtd_temp\n"; }
  				
  				if (${sub_folder_name} eq "xuikon") { # generate xuikon .dtd files to temp path
  					if ($debug) { print "Widget type DTD, xuikon subfolder\n"; }
  				  process_dtd($temp_loc_files_path, $lang_id);
  			  } else{ #hsps folder
  			  	if ($debug) { print "Widget type DTD, hsps subfolder\n"; }
	  				process_dtd($full_dtd_output_path, $lang_id);
  			  }  			  
  		} elsif ((${sub_folder_name} eq "xuikon") && ($force_create ne "") && (-d $dtd_temp)) {
  			copy_files($dtd_temp,"${temp_loc_files_path}\\${lang_id}");
  		}
		}
		
		if (${sub_folder_name} eq "xuikon") { # generate localized files
			if (!(-f $themeinstaller_tool)) { die("ERROR: dtd_installer.pl, can not find themeinstaller: $themeinstaller_tool\n");	}
			if (!(-f $themeinstaller_property_file)) { die("ERROR: dtd_installer.pl, can not find themeinstaller property file: $themeinstaller_property_file\n");	}
			
	  	if (-d $temp_loc_files_path) {
	  		opendir(SDIR, $temp_loc_files_path) or die("ERROR: dtd_installer.pl, can not open $temp_loc_files_path\n");
				@lang_dirs = grep !/^\.\.?$/, readdir SDIR;
	  		closedir(SDIR);
		  	
		  	foreach my $lang_id (@lang_dirs) {		
		  		my $lang_dir = "$temp_loc_files_path\\$lang_id";
		  		if ($debug) { print"Language directory:\n$lang_dir\n"; }
		  		if (-d $lang_dir) { # Running themeinstaller for all language folders in temp path
		  			my $temp_dir = "$temp_dtd_path\\$lang_id";
		  			copy_files($full_dtd_input_path, "$temp_dir");
		  			my $lang_temp_dir = "$full_dtd_input_path\\$lang_id";
		  			if (-d $lang_temp_dir) {
		  				copy_files("$lang_temp_dir", "$temp_dir");
		  			}
		  			copy_files("$temp_loc_files_path\\$lang_id", "$temp_dir");
	  			  if  (($action_type eq "build") || ($debug)) {	
	  			  	print ("Calling themeinstaller: \n$themeinstaller_tool $temp_dtd_path\\${lang_id}\\${dtd_name}.dat $temp_dtd_path\\${lang_id} -prop:${themeinstaller_property_file}\n"); 
	  			  	system ("$themeinstaller_tool","$temp_dtd_path\\${lang_id}\\${dtd_name}.dat","$temp_dtd_path\\${lang_id}", "-prop:${themeinstaller_property_file}");
	  			  } else {
	  			  	system ("$themeinstaller_tool","$temp_dtd_path\\${lang_id}\\${dtd_name}.dat","$temp_dtd_path\\${lang_id}", "-prop:${themeinstaller_property_file}", ">$temp_dtd_path\\${lang_id}\\themeinstaller.log", "2>&1" );
	  			  }
	  				copy_files("$temp_dir", "$full_dtd_output_path\\$lang_id", "recursive");
		  		}
		  	}
		  }
	  }
	  
	  if ($debug) { 
	  	print "Widget processed: ${dtd_name} \n"; 
	  } else {
		  # Remove all temporary directories
			if (-d $temp_dtd_path) { rmtree ($temp_dtd_path);	}
			if (-d $temp_loc_files_path) { rmtree ($temp_loc_files_path);	}
			rmdir $temp_path;
			rmdir $temp_loc_path;
		}
	}
}

sub process_dtd {
	
	my $output_path = shift;
	my $switch_loc_name = shift;
	$switch_loc_name =~ s/.dtd//i;; # remove the .dtd extension
	my $input_path = $dtd_location;
	my ($found, $loc_file);
	if ($action_type eq "build") { print "Used switch loc file name:\n${switch_loc_name}\n"; }
	if ($debug) { print "Used input path:\n${input_path}\n"; }
	if ($debug) { print "Used output path:\n${output_path}\n"; }
	
	foreach (@layers) {
		$input_path = $_;
			if ($debug) { print("Used switch loc file path:\n${input_path}\n"); }
			my $loc_file = "${input_path}\\${switch_loc_name}.loc";
			if (-e $loc_file) {
				convert_locs_to_dtds($loc_file, $input_path, $output_path);
				$found = "yes";
			} 
		}
		if ($found ne "yes") {
			warn "ERROR: dtd_installer.pl, no .loc file found:\n${switch_loc_name}.loc\n";
		}
}

sub check_options {
	
	if ($dtd_name eq "") {
		warn: "ERROR: dtd_installer.pl, no widget name given!!!\nDtd_installer\.pl script stopped\n";
		die;
	}

	if ($dtd_type eq "") {
		$dtd_type = "dtd";
	}

	if ($dtd_location eq "") {
		if ($dtd_type eq "widget") {
			$dtd_location = "\\epoc32\\data\\z\\resource\\homescreen";
		}
	} else {
		if ($dtd_type eq "dtd") {
		  undef @layers;
	 	 	@layers[0]=${dtd_location};
	 	}
	}
	
	if ($output_location eq "") {
		$output_location = "\\epoc32\\release\\winscw\\udeb\\z\\private\\200159c0\\install";
	}
	
	if (${sub_folder_name} ne ""){
	  undef @sub_folders;
	  @sub_folders[0]=${sub_folder_name};
  }

	if ($action_type eq "") {
		$action_type = "build";
	} 
	
	$dtd_location =~ s/\//\\/g;    #Change / marks to \
	$output_location =~ s/\//\\/g;    #Change / marks to \
	$what_output_file = $output_location;
	$what_output_file =~ s/\\/_/g; #Change \ marks to _
	$what_output_file =~ s/:/_/g; #Change : marks to _
	if ($ENV{SBS_BUILD_DIR}) { 
		$what_output_file = $ENV{SBS_BUILD_DIR} . "${PATHSEP}dtd_installer${PATHSEP}" . $what_output_file . $dtd_name . ".txt";
		if ( !-d $ENV{SBS_BUILD_DIR} . "${PATHSEP}dtd_installer") { mkdir($ENV{SBS_BUILD_DIR} . "${PATHSEP}dtd_installer"); }		
	}
	else {
		$what_output_file = $EPOCROOT . "${PATHSEP}epoc32${PATHSEP}build${PATHSEP}dtd_installer${PATHSEP}" . $what_output_file . $dtd_name . ".txt";    
		if ( !-d "/epoc32/build/dtd_installer") { mkdir("/epoc32/build/dtd_installer"); }
	}
	
	if ($debug) { print "Output what file: $what_output_file\n"; }
}

# This subroutine moves files to/from temporary themeinstaller location.
sub copy_files {
    my $in_path = shift;
    my $out_path = shift;
    my $recursive = shift;
	 	if ($debug) { print "Copying from: $in_path\n"; }
	 	if ($debug) { print "To: $out_path\n"; }
    
    if ($recursive) {
  	  	find( \&getFiles, $in_path );
  	} else {
				opendir(SDIR, $in_path) or die("ERROR: dtd_installer.pl, can not open $in_path\n");
				@find_files = grep !/^\.\.?$/, readdir SDIR;
				closedir(SDIR);  	
		}
		
		foreach my $file (@find_files) {
				my $in_file = "${in_path}\\${file}";
				my $out_file= "${out_path}\\${file}";			
				if ($recursive) {
					$in_file = $file;
		    	$file =~ /.*\\(.*)\\.*\\.*\\.*\\(.*)\\(.*)/i;  	
		    	my $temp=$1; # lang code	
		    	my $temp2=$3;	# file name
		    	if ((lc $2) eq "sources") {
		    		$out_file = "${out_path}\\$3";
		    	} else {
		    		if (length($temp) > 5) { #skip extra files
		    			next;
		    		}
            while (length($temp) < 4){ $temp = "0".$temp; }
			    	$temp2 =~ s/\d{4}/$temp/g; # change .odt filename for correct lang
		    		$out_file = "${out_path}\\$temp2";
		    	}
	  		}
				if ($debug) { print "Copying file from: $in_file\n"; }
			 	if ($debug) { print "To: $out_file\n"; }
				if (-f $in_file){
					if ($action_type eq "build") {
						if ((!($out_file =~ /\\temp\\/i))) {write_what_file("$out_file")};
						xcopy($in_file,$out_file);
					} elsif ($action_type eq "clean") {
						if (!($out_file =~ /\\temp\\/i)) {
							unlink $out_file;
							my $temp_dir_path = $out_file;
							$temp_dir_path =~ /(.*)\\.*/;
							$temp_dir_path = $1;
							rmdir $temp_dir_path; # Try to remove empty language directories
						} else {
							xcopy($in_file,$out_file);
						}
					} elsif ($action_type eq "what") {
						if (!($out_file =~ /\\temp\\/i)) {
							write_what_file("$out_file");
							print("$out_file\n");
						} else {
							xcopy($in_file,$out_file);
						}
					} else {
						warn ("ERROR: dtd_installer.pl, unknown action type");	
					}
		 		} else {
		 				if ($debug) { print "Not file found: $in_file\n"; }
		 		}
 		}	
}

# This subroutine converts LOC files to DTD files. Files that are  
# listed in the switch_loc file are converted to DTD files.

sub convert_locs_to_dtds {
    my $switch_loc_file = shift;
    my $in_path = shift;
    my $out_path = shift;
        
    open(my $switch_loc_file_handle, "$switch_loc_file") 
    or die "Can't open `$switch_loc_file' for reading: $!";
    
    # Read localised .loc file names from used input switch loc file
    while (my $line = <$switch_loc_file_handle>) {
        chomp($line);
        if (($line =~ "include") && (!($line =~ /\<sc\//i)) && (!($line =~ /\<00\//i)) ){ # Read all lines that contains include, except sc and 00
	       	$line=~ /.*\<(.*)\>.*/;
  	     	$line=$1;
        	$line =~ s/\//\\/g;    #Change / marks to \
        	if ($debug) { print"Adding localised file to conversion list:\n$line\n"; }
        	push @files_to_convert, $line;
        }
    }
    
    close $switch_loc_file_handle;
    
  # Process all the .loc files.
  foreach (@files_to_convert) {
  	my $loc_file = "$in_path\\$_";
  	my $out_file = "$out_path\\$_";
  	$out_file =~ s/_\d{2,5}(.{4})$/$1/i; # remove the language code from the file name.
    if ($debug) { print"Trying to convert file:\n$loc_file\n"; }
		if ($debug) { print"To out file:\n$out_file\n"; }
    if (-f $loc_file) {
			if (($action_type eq "build") || ((${dtd_type} eq "widget") && (${sub_folder_name} eq "xuikon")) ) {
#old 				if ((!($out_file =~ /\\temp\\/i))) {write_what_file("$out_file")};
				xcopy($loc_file,$out_file);
    			Convert_file::convert_file($out_file);
				if ((!($out_file =~ /\\temp\\/i))) {
					my $convert_out_file = $out_file;
					$convert_out_file =~ s/\.loc/\.dtd/; # replace .loc with .dtd 
					write_what_file("$convert_out_file");
				}
		  		if (!($debug)) { unlink $out_file; } # Delete the copied .loc file
		  		$out_file =~ s/\.loc/\.log/; # replace .loc with .log
		  		if (!($debug)) { unlink $out_file; } # Delete the conversion .log file
			} elsif ($action_type eq "clean") {
				$out_file =~ s/\.loc/\.dtd/; # replace .loc with .dtd
				unlink $out_file; # delete the output file
				my $temp_dir_path = $out_file;
				$temp_dir_path =~ /(.*)\\.*/;
				$temp_dir_path = $1;
				rmdir $temp_dir_path; # Try to remove empty language directories
			} elsif (($action_type eq "what") && (!($out_file =~ /\\temp\\/i))) {
				$out_file =~ s/\.loc/\.dtd/; # replace .loc with .dtd
				print("$out_file\n");
				write_what_file("$out_file");
			}
    } else {
   		warn "ERROR: dtd_installer.pl, no .loc file found: $loc_file\n";
   	}
  }
}

# This subroutine is for file copying
sub xcopy
{
    my $source = shift;
    my $dist = shift;
    
    # if distination file exist then clear read flag
    if (-f $dist)
    {
        chmod ($dist , 0755);
    }
    else
    {
        my($n, $d, $ext) = fileparse($dist, '\..*');
        # check weather distination directory exist or not. If directory doesn't exist then create it.
        -d $d || mkpath($d, 0, 0x755);
    }
    
    # copy source to distination
    copy($source,$dist);
}

# read files from given path to filelist
sub getFiles {
	my $file_name = $File::Find::name;
	$file_name =~ s/\//\\/g;    #Change / marks to \
	chomp $file_name;
	next if ( -d $file_name ); # Skip directories
	next if ((!($file_name =~ /o0000/i)) && (!($file_name =~ /\\sources\\/i))); # Skip other then resource and source files
	push @find_files, $file_name;
}

sub write_what_file {
	my $out = shift;
	open( WHAT, ">>$what_output_file") or die $!;
		print WHAT "$out\n";
	close WHAT;
	
}
