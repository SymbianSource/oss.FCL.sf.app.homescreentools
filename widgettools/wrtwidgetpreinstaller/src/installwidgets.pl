#
# Copyright (c) 2010 Nokia Corporation and/or its subsidiary(-ies).
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

use strict;
use warnings;
use File::Spec::Functions;
use Getopt::Long;
use Pod::Usage;

# Version of the script - just use the date
$main::VERSION = '02-August-2010';

# New getopt::long provides this - but old version doesn't?
sub version
  {
  print sprintf("$0: $main::VERSION\n$^X: %vd\nos: $^O", $^V);
  exit;
  }

# Get arguments
my ( $help, $version, $verbose, $debug, $epocroot, $l10n );
GetOptions( "help" => \$help, "version|ver" => \$version,
      "verbose|v" => \$verbose,  "debug" => \$debug,
      "epocroot|e=s" => \$epocroot, "localization|l=s" => \$l10n )
  or pod2usage('Invalid parameters');

# Handle help and version
pod2usage({ verbose => 1, exitval => 0}) if $help;
version() if $version;

# Interpret arguments
$verbose = 1 if $debug;
$verbose = $verbose ? '-v' : '';
$epocroot = $ENV{EPOCROOT} if !$epocroot;

# Interpret localization l10n argument

# There are two modes.  In one mode you specify the location of a
# lproj.xml file and the code computes l10n files for all languages so
# that runtime locale selection should work.  In the other mode you
# specify a language code (example, fr for French) and the code
# computes l10n just for that language.
$l10n = '' if !$l10n;
my $lproj = '';
if ($l10n =~ /lproj\.xml$/i)
  {
  $lproj = $l10n;
  $l10n = '';
  }

my ($configini, @unnecessary) = @ARGV;

if ($configini)
  {
  # There shouldn't be any need for any other arguments
  pod2usage('Unnecessary arguments supplied.') if @unnecessary;

  # Now do the installation
  my $installer = WidgetInstaller->new('verbose' => $verbose, 'debug' => $debug, 'epocroot' => $epocroot, 'lproj' => $lproj, 'l10n' => $l10n);
  $installer->installConfig($configini);
  }
else
  {
  pod2usage('Missing config.ini argument.');
  }

# ***
# Package for installing Widgets
#

package WidgetInstaller;

use File::Spec::Functions;
use File::Path;
use File::Basename;
use Unicode::String qw(utf8 utf16);
use File::Temp qw/tempdir/;
use File::Copy;
use XML::Parser;
use Data::Dumper;
use XML::Simple;

# CONSTANTS
use constant ICON_SIZES => "88,32,24";      # Size of icons to generate in the MBM file
#use constant INTERNAL_UID_LOWER => 0x2000DAD2; # Lower UID bound for midlets installed to internal drives and rom
#use constant EXTERNAL_UID_LOWER => 0x2000DCC6; # Lower UID bound for midlets installed to removable cards
use constant INTERNAL_UID_LOWER_WRT => 0x2000DAD2;  # Lower UID bound for WRT widgets installed to internal drives and rom
use constant INTERNAL_UID_LOWER_CWRT => 0x2000DBCC; # Lower UID bound for CWRT widgets installed to internal drives and rom
use constant EXTERNAL_UID_LOWER_WRT => 0x2000DCC6;  # Lower UID bound for WRT widgets installed to removable cards
use constant EXTERNAL_UID_LOWER_CWRT => 0x2000DDC0; # Lower UID bound for CWRT widgets installed to removable cards
use constant WIDGET_UI_UID => 0x10282822;   # UID of the widget app
use constant CWRT_WIDGET_UI_UID => 0x200267C0;    # UID of the cwrt widget app
use constant SWIDGET_UI_UID => 0x102829A0;	# UID of the securewidget app
use constant CWRT_WIDGET_UI_NON_NOKIA_UID => 0x200267D6;    # UID of the cwrt widget app
use constant JIL_NS => 'http://www.jil.org/ns/widgets1.2';

# Folder paths
use constant DESTINATION => 'private/10003a3f/import/apps/NonNative/Resource';
use constant ROM_DEST => 'epoc32/release/winscw/udeb/Z/';
use constant DRIVE_DEST => 'epoc32/winscw/%s';
use constant WIDGET_REGISTRY => 'private/10282f06/WidgetEntryStore.xml';
use constant CWRT_WIDGET_REGISTRY => 'private/10282f06/CWRTWidgetEntryStore.xml';
use constant CWRT_WEBAPP_REGISTRY => 'private/200267D9/webapp_registry.db';
use constant CWRT_ACCESS_POLICY_PATH => 'browser_access_policy.xml';
use constant WIDGET_NAME => 'en-gb/widget/name';
use constant WIDGET_PROCESSUID => 'processUid';
use constant WIDGET_ID => 'widget/id';
use constant WIDGET_VERSION => 'widget/version';
use constant WIDGET_CONTENT => 'widget/content';
use constant WIDGET_FEATURE => 'widget/feature/';
use constant WIDGET_FEATURE_PARAM => '/param/';
use constant WIDGET_ACCESS => 'widget/access/';
use constant WIDGET_HEIGHT => 'widget/height';
use constant WIDGET_WIDTH => 'widget/width';
use constant WIDGET_NOKIA_SHAREDLIB => 'widget/NOKIA:sharedlibrary';
use constant WIDGET_NOKIA_SHAREDLIB_FOLDER => 'widget/NOKIA:sharedlibrary/NOKIA:folder';
use constant WIDGET_NOKIA_SHAREDLIB_WIDGET => 'widget/NOKIA:sharedlibrary/NOKIA:widget';
use constant WIDGET_NOKIA_SHAREDLIB_ICON => 'widget/NOKIA:sharedlibrary/NOKIA:icon';
use constant KEY_VALUE_SEPERATOR => ',';
use constant KEY_VALUE_PAIR_SEPERATOR => ';';
use constant KEY_ATTR_SEPERATOR => ':';

our $w3c_widget = 0 ;
our $hashval;
our $non_nokia_widget = 0;
our ($isSharedLibrary, $sharedFolderName ,$isSharedWidget, $isSharedIcon)= (0,'',0,0);
our (@staticUidWrtIntList,@staticUidCwrtIntList,@staticUidWrtExtList,@staticUidCwrtExtList) = ({},{},{},{});
our $isSecureWidget = 0;

# Create a new object
sub new
  {
  my $invocant = shift;
  my $self = bless({}, ref $invocant || $invocant);

  my %args = @_;
  $self->{'args'} = \%args;
  $self->{'args'}->{'verbose'} = $self->{'args'}->{'verbose'} ? '-v' : '';

  $self->{'installedFiles'} = ();
  $self->{'freeuidwrtint'} = INTERNAL_UID_LOWER_WRT;
  $self->{'freeuidwrtext'} = EXTERNAL_UID_LOWER_WRT;
  $self->{'freeuidcwrtint'} = INTERNAL_UID_LOWER_CWRT;
  $self->{'freeuidcwrtext'} = EXTERNAL_UID_LOWER_CWRT;
  $self->{'langmapping'} = $self->getLangMapping($self->{'args'}->{'lproj'}) unless $self->{'args'}->{'l10n'};
  
  #Check if localisation argument is land number ID; If true, get the lang Name using langmapping file - Widget_lproj.xml 
  if ($l10n =~ /\d+$/)
  {
    print "\nLANG ID given as localisation argument :: $l10n \n";
    $self->{'langmapping'} = $self->getLangMapping();
    
    if($self->{'langmapping'})
    {
      # Iterate through all the languages we know about
      for(my $i = 0; $i < scalar(@{ $self->{'langmapping'}->{LangID} }); $i++)
      {
        my ( $langid, $langname ) = ( $self->{'langmapping'}->{LangID}->[$i], $self->{'langmapping'}->{LangDir}->[$i] );
        if($l10n == $langid)
        {
          print "Setting argument to LangName - $langname \n";
          $self->{'args'}->{'l10n'} = lc($langname);
          last;
        }
      }
    }
  }

  return $self;
  }
  
# Gets the language mapping from the Widget_lproj.xml file
sub getLangMapping
  {
  my ( $self, $lproj ) = @_;

  # Get the LPROJ file which specifies lang id mappings
  if (!$lproj)
    {
    (my $EPOCROOT = $ENV{EPOCROOT}) =~ s/[\/\\]+$//;
    $lproj = WidgetInstaller::fixFilename("${epocroot}epoc32/winscw/c/private/10282f06/Widget_lproj.xml");
    $lproj = WidgetInstaller::fixFilename("$EPOCROOT/epoc32/winscw/c/private/10282f06/Widget_lproj.xml") if !-e $lproj;
    $lproj = WidgetInstaller::fixFilename("${epocroot}epoc32/data/Z/private/10282f06/Widget_lproj.xml") if !-e $lproj;
    $lproj = WidgetInstaller::fixFilename("$EPOCROOT/epoc32/data/Z/private/10282f06/Widget_lproj.xml") if !-e $lproj;
    $lproj = WidgetInstaller::fixFilename("${epocroot}S60/mw/web/WebEngine/WidgetRegistry/Data/Widget_lproj.xml") if !-e $lproj;
    $lproj = WidgetInstaller::fixFilename("$EPOCROOT/S60/mw/web/WebEngine/WidgetRegistry/Data/Widget_lproj.xml") if !-e $lproj;
    $lproj = WidgetInstaller::findCmd('Widget_lproj.xml') if !-e $lproj;
    $lproj = WidgetInstaller::findCmd('internal/Widget_lproj.xml') if !-e $lproj;
    undef $lproj if !-e $lproj;

    # Display a warning if localisation can't be performed
    warn "WARNING: Can't find Widget_lproj.xml - localisation is disabled.\n" if !$lproj;
    }

  # Load the mapping file
  if ($lproj)
    {
    die "Can't find $lproj file." if !-e $lproj;
    print "Localisation support enabled using config: $lproj\n" if $verbose;
    my $mapping = XMLin($lproj);
    print "Found ", scalar(@{ $mapping->{'LangID'} }), " language mappings.\n" if $verbose;
    return $mapping;
    }
  }

# Install Widgets listed in config file
# Format is as follows where "drive-z" specifies widgets for drive z: etc...
# Comments are okay - they start with a # character
# If the file doesn't exist as given then EPOCROOT is prepended to the filename to try and find it
#
# You can specify whether a widget is intended for the homescreen by adding the text [HomeScreen] after the filename
# This will set the BlanketPermissionGranted attribute in the registry.
# Widgets intended for the homescreen must have the MiniViewEnabled attribute set in its PLIST file otherwise an error is generated.
#
# You can specify commands to run before exit after a [run-commands] or [homescreen-processor] 
#
# [drive-z]
# \path\widget1.wgz
# widget2.wdgt.zip [HomeScreen]
#
# [drive-e]
# widget3.wgz
#
# [run-commands]
# dostuff.pl
#

sub installConfig
  {
  my ( $self, $file ) = @_;
  $self->{'installedFiles'} = ();

  my ( %installData, $sectionName );
  open CONFIG, $file or die "Failed to open config file $file: $!";
  
  # Loop for gathering STATIC UIDs allocated for widgets in config INI file
  while(my $line = <CONFIG>)
  {
    # Ignore comments
    $line =~ s/\#.*$//;
    
    if ($line =~ /^\[([^\]]+)\]/)
      {
      $sectionName = lc $1;
      next;
      }

    # Process sections after this point
    next if !$sectionName;
    chomp $line;

    # Have we found a list of widgets?
    if ($sectionName =~ /^drive-([a-z])/)
    {
      my $drive = uc($1);
      #Assuming Static UID given in ini are within int/ext/wgt/wgz specified ranges
      # Add Static UID to the respective list
      if ($line =~ /^(.+?\.(?:wdgt\.zip|wgz|wgt))\s*(\[HomeScreen\])?\s*(0x[a-fA-F0-9]{8})?\s*(\[Operator\])?\s*$/i)
      {
        if ($3)
        {
          my $uid = hex($3);
          
          if ($drive =~ /^[zcZC]/)
          {
            if(($uid >= INTERNAL_UID_LOWER_WRT) && ($uid < INTERNAL_UID_LOWER_CWRT))
            {
              push(@staticUidWrtIntList,$uid) ;
            }
            else
            {
              push(@staticUidCwrtIntList,$uid);
            }
          }
          else
          {
            if(($uid >= EXTERNAL_UID_LOWER_WRT) && ($uid < EXTERNAL_UID_LOWER_CWRT))
            {
              push(@staticUidWrtExtList,$uid) ;
            }
            else
            {
              push(@staticUidCwrtExtList,$uid) ;
            }
          }
        }
      }
    }
  }
  close CONFIG;
  @staticUidWrtIntList = sort(@staticUidWrtIntList);
  print "SORTED WRT INTERNAL STATIC UID  @staticUidWrtIntList \n";
  @staticUidCwrtIntList = sort(@staticUidCwrtIntList);
  print "SORTED CWRT INTERNAL STATIC UID  @staticUidCwrtIntList \n";
  @staticUidWrtExtList = sort(@staticUidWrtExtList);
  print "SORTED WRT EXTERNAL STATIC UID @staticUidWrtExtList \n";
  @staticUidCwrtExtList = sort(@staticUidCwrtExtList);
  print "SORTED CWRT EXTERNAL STATIC UID @staticUidCwrtExtList \n";
  
  open CONFIG, $file or die "Failed to open config file $file: $!";
  # Main loop which reads the config INI line by line and installs widgets[wgz/wgt] in respective drives
  while(my $line = <CONFIG>)
    {
    # Ignore comments
    $line =~ s/\#.*$//;

    if ($line =~ /^\[([^\]]+)\]/)
      {
      $sectionName = lc $1;
      
      # Remember destination if any specified
      if ($sectionName =~ /^drive-([a-z])=(.+)$/)
        {
        $self->{'destination'}->{uc($1)} = $2;
        }
      next;
      }

    # Process sections after this point
    next if !$sectionName;
    chomp $line;

    # Have we found a list of widgets?
    if ($sectionName =~ /^drive-([a-z])/)
      {
      my $drive = uc($1);
      
      # Add to the list of Widget files
      if ($line =~ /^(.+?\.(?:wdgt\.zip|wgz|wgt))\s*(\[HomeScreen\])?\s*(0x[a-fA-F0-9]{8})?\s*(\[Operator\])?\s*$/i)
        {
        my $widget = $1;
        $widget = fixFilename(catfile($self->{'args'}->{'epocroot'}, $1)) if !-e $widget;
        die "Can't find widget $widget" if !-e $widget;
        $self->{'homescreen'}{lc $widget} = 1 if $2; # Intended for the homescreen?
        $self->{'staticUID'}{lc $widget} = hex($3) if $3;
        $self->{'secure'}{lc $widget} = 0;
        $self->{'operator'}{lc $widget} = 1 if $4;
        print "Widget for drive $drive: $widget\n" if $self->{'args'}->{'verbose'};
        push @{ $installData{"$drive:"} }, $widget;
        }
      elsif ($line =~ /^(.+?\.(?:wdgt\.zip|wgz))\s*(\[Secure\])?\s*(0x[a-fA-F0-9]{8})?\s*$/i)
        {
          my $widget = $1;
          $widget = fixFilename(catfile($self->{'args'}->{'epocroot'}, $1)) if !-e $widget;
          die "Can't find widget $widget" if !-e $widget;
          $self->{'secure'}{lc $widget} = 1 if $2; # Intended for a secure widget handling?
          $self->{'staticUID'}{lc $widget} = hex($3) if $3;
          print "Widget for drive $drive: $widget\n" if $self->{'args'}->{'verbose'};
          push @{ $installData{"$drive:"} }, $widget;
        }
      else
      	{
      		my $widget = $1;
      		$self->{'secure'}{lc $widget} = 0;
        }	
      }
    # Retrieve the command to execute before exit
    elsif ($sectionName =~ /^(run-commands|homescreen-processor)$/i && $line)
      {
      push @{ $self->{'exitcmds'} }, $line;
      }
    }
  close CONFIG;

  # Now intall the widgets for each drive specified in the config file
  foreach my $drive ( keys %installData )
    {
    $self->installFiles($drive, $installData{$drive} );
    $self->makeIBY($drive);
    $self->makeIBY($drive, 'localised') unless $self->{'args'}->{'l10n'};
    }
  
  # Exit commands at the end of the process
  if ($self->{'exitcmds'})
    {
    foreach my $cmd ( @{ $self->{'exitcmds'} } )
      {
      print "Executing: $cmd\n" if $self->{'args'}->{'verbose'};
      warn "WARNING: error running $cmd" if system($cmd) != 0;
      }
    }
  }

# ***
# Installs files to a drive
#
sub installFiles
  {
  my ( $self, $drive, $fileList ) = @_;
  my $startsrc ;
    my $iconsrc ;
  
   $isSharedLibrary = 0;
   $isSharedWidget = 0;
   $isSharedIcon = 0;
   $sharedFolderName ='';
   $isSecureWidget = 0;
    
  print "Installing files for drive $drive\n" if $self->{'args'}->{'verbose'};

  # Unregister any existing widgets as otherwise when the registry is rewritten their icons will appear in the emulator but they won't work
  $self->unregisterWidgets($drive);

  print "\n     INSTALLING FILES FOR DRIVE $drive       \n";
  # Process each widget in turn
  my ( @installedProps );
  my ( @installedCWRTProps );
  foreach my $filename ( @$fileList )
    {
    # Check the file exists
    die "Can't find $filename" if !-e $filename;

    # Create a temporary folder
    print "\nInstalling $filename\n";
    my $tempdir = tempdir ( DIR => '.', CLEANUP => !$self->{args}->{'debug'});

    # Prefer to use 7zip rather than unzip because it's better behaved wrt Unicode
    if (findCmd('7z.exe'))
      {
      $self->un7zipWidget($filename, $tempdir);
      }
    else
      {
      $self->unzipWidget($filename, $tempdir);
      }
        my $widgetdata ;
        
        $isSharedLibrary = 0;
        $isSharedWidget = 0;
        $isSharedIcon = 0;
        $sharedFolderName ='';
    
    my ( $root, $extracted, $size ) = $self->getFiles($tempdir);
    die "No files extracted from $filename" if !@$extracted;
    
    if ($self->{'operator'}{lc $filename})
    {
      print "\nNON NOKIA WGT \n";
      $non_nokia_widget = 1;
    }
    else
    {
      print "\nNOKIA WGT \n";
      $non_nokia_widget = 0;
    }
    
    
    if (($filename =~ /.wgz/ )&& (my $plist = catfile($tempdir, $root, 'Info.plist')))
      {
          print ("S60 widget \n");
          
          $w3c_widget = 0;
          # Parse the XML file into a hash
              $widgetdata = parsePList($plist);
      }
    elsif (($filename =~ /.wgt/ ) && ( my $confxml = catfile($tempdir, $root, 'config.xml')))
      {
        print ("W3C widget \n");

          # Parse the XML file into a hash
            $widgetdata = parseConfXml($confxml,$self->{'args'}->{'l10n'});
            $w3c_widget = 1;
      }
    else
      {
      die "Can't find $root/Info.plist , $root/config.xml file";
      }       
		
	  if ($self->{'secure'}{lc $filename}){
		$isSecureWidget = 1;
	  } else {
	  	$isSecureWidget = 0;
	  }

    if( $w3c_widget )
    { 
      if( $widgetdata->{'MainHTML'} )
        {
        $startsrc = $widgetdata->{'MainHTML'};
        }
      else
        {
        $startsrc = 'index.html';
        }
      if( $widgetdata->{'IconPath'} )
        {
        $iconsrc = $widgetdata->{'IconPath'};
        }
      else
        {
        $iconsrc = 'icon.png';   
        }
        
  		if($non_nokia_widget)
  		{
  			$widgetdata->{'ProcessUid'} = CWRT_WIDGET_UI_NON_NOKIA_UID;
  		}
  		else
  		{
      		$widgetdata->{'ProcessUid'} = CWRT_WIDGET_UI_UID;
      	}
      
      $widgetdata->{'MimeType'} = "application/widget";
    }         

    print "Identifier: $widgetdata->{'BundleIdentifier'}\n" if $self->{args}->{'verbose'};
    
    # Set widget package properties
    $widgetdata->{'FileName'} = $filename;
    $widgetdata->{'FileSize'} = $size;

    # Load the language translations for BundleDisplayName
    if ($self->{'args'}->{'l10n'})
      {
      my $localised = $self->getLocalisedStringByLangCode(catfile($tempdir, $root), 'DisplayName', $self->{'args'}->{'l10n'});
      $widgetdata->{'BundleDisplayName'} = $localised if $localised;
      }
    else
      {
      $widgetdata->{'LocBundleDisplayName'} = $self->getLocalisedStrings(catfile($tempdir, $root), 'DisplayName');
      }

    # Fix up some of the fields
    $widgetdata->{'BundleName'} = $widgetdata->{'BundleDisplayName'} if !$widgetdata->{'BundleName'};
    $widgetdata->{'AllowNetworkAccess'} = $widgetdata->{'AllowFullAccess'} if !$widgetdata->{'AllowNetworkAccess'};
    $widgetdata->{'DriveName'} = $drive;
    
    if( $w3c_widget )
      {
      $widgetdata->{'PropertyListVersion'} = 4;
      my $widget_uid;
      
      if($non_nokia_widget)
  		{
  			$widget_uid = CWRT_WIDGET_UI_NON_NOKIA_UID;
  		}
  		else
  		{
      	$widget_uid = CWRT_WIDGET_UI_UID;
      }
      
      if($isSharedLibrary)
      {
        #In case of NOKIA:sharedlibrary, the extracted widget contents and data source are stored under private\<uid>\..\lib\<sharedfoldername>\
        $widgetdata->{'BasePath'} = sprintf('%s\\private\\%08X\\%s\\%s\\%s\\', $widgetdata->{'DriveName'}, $widget_uid, "widgets_21D_4C7","lib",$sharedFolderName);
        $widgetdata->{'IconPath'} = sprintf('%s\\private\\%08X\\%s\\%s\\%s\\',$widgetdata->{'DriveName'}, $widget_uid, "data" ,"lib" ,$sharedFolderName);
      }
      else
      {
        $widgetdata->{'BasePath'} = sprintf('%s\\private\\%08X\\%s\\%s\\', $widgetdata->{'DriveName'}, $widget_uid, "widgets_21D_4C7", hashpjw($widgetdata->{'BundleIdentifier'}));
        $widgetdata->{'IconPath'} = sprintf('%s\\private\\%08X\\%s\\%s\\',$widgetdata->{'DriveName'}, $widget_uid, "data" , hashpjw($widgetdata->{'BundleIdentifier'}));
      }
      $widgetdata->{'MainHTML'} = "$widgetdata->{'BasePath'}$startsrc";
      $widgetdata->{'AllowNetworkAccess'} = 1;
      
      }
    else
      {
      $widgetdata->{'PropertyListVersion'} = 1;
      $widgetdata->{'BasePath'} = sprintf('%s\\private\\%08x\\%s\\', $widgetdata->{'DriveName'}, WIDGET_UI_UID, $widgetdata->{'BundleIdentifier'});
      $widgetdata->{'MainHTML'} = "$widgetdata->{'BasePath'}$root\\$widgetdata->{'MainHTML'}";
      $widgetdata->{'IconPath'} = "$widgetdata->{'BasePath'}$root\\";
      }
      
    $widgetdata->{'BlanketPermissionGranted'} = 0 if( ! $widgetdata->{'BlanketPermissionGranted'} );
    $widgetdata->{'MiniViewEnabled'} = 0  if( ! $widgetdata->{'MiniViewEnabled'} );
    
    # Indicate that the widget was pre-installed
    $widgetdata->{'PreInstalled'} = 1;
    
    # Set BlanketPermissionGranted flag if Widget is listed as a homescreen widget in the INI file
    # Error if MiniViewEnabled isn't set
    if ($self->{'homescreen'}{lc $filename})
      {
      $widgetdata->{'BlanketPermissionGranted'} = 1;
      die "ERROR: $filename - MiniViewEnabled not set for homescreen widget" if !$widgetdata->{'MiniViewEnabled'};
      }

    # Defining UID  
    if($self->{'staticUID'}{lc $filename})
      {
      print "Using Static UID from INI file\n";
      $widgetdata->{'Uid'} = $self->{'staticUID'}{lc $filename};
      }
    else
      {
      # Find the next free UID to use
      $widgetdata->{'Uid'} = $self->findfreeUid($widgetdata);
      }
    print sprintf("Using UID for midlet: 0x%08X\n", $widgetdata->{'Uid'}) if $self->{args}->{'verbose'};

    # Make sure the destination exists
    my $dest = $self->regFileName($drive);
    mkpath $dest;

    my $icon;
    if($w3c_widget)
    {
      my $locate = $self->{'args'}->{'l10n'};
      my $seperator ='-';
      my $position = -1;
      my $found = 0 ;
      if ($self->{'args'}->{'l10n'})
          {
            do
               {
                my $searchdir = '.\\'.$tempdir.'\\locales\\'.$locate;
                if( opendir(DIR, $searchdir))
                    {
                    my @files = grep(/$iconsrc$/,readdir(DIR));
                    closedir(DIR);
                    if(@files)
                       {
                        $iconsrc = 'locales\\'.$locate.'\\'.$iconsrc ;
                        $found = 1;
                       }
                    }  
                if(($position = rindex($locate,$seperator)) > 0 )
                    {
                    $locate = substr($locate,0,$position);
                    }
               } while (!$found && $position > 0);
          }
          if ($iconsrc)
          {
            $icon = catfile($tempdir, $root, $iconsrc);    
          }
            
          if(-e $icon)
          {
             $widgetdata->{'DBIconPath'}= "$widgetdata->{'BasePath'}$iconsrc";
             print "Icon found -- $widgetdata->{'DBIconPath'} \n";
          }
          else
          {
              $icon = findCmd('default_widget_icon.png');
              print "default_widget_icon.png used \n";    
              $widgetdata->{'DBIconPath'}= ":/resource/default_widget_icon.png";
          }
      }
    else
    {
      $icon = catfile($tempdir, $root, 'Icon.png');
            die "ERROR: Widget bundle must include an Icon.png file in $root directory.\n" unless -e $icon;
    }
    
    # Create the MBM file icon - in case of sharedlibrary, create only if NOKIA:widget is true
    my $mbm;
    
    print("\nIs shared library - $isSharedLibrary \nIs sharedlib widget - $isSharedWidget \nIs Secure WGZ - $self->{'secure'}{lc $filename}\n");

    if( ((!$isSharedLibrary) || ($isSharedLibrary && $isSharedIcon)) && (!$self->{'secure'}{lc $filename}))
    {
    	  print "Creating mbm !!!\n";
        die "ERROR: Can't find PNG2MBM command in PATH." if !(my $cmd = findCmd('png2mbm.exe'));
        $mbm = $self->regFileName($drive, sprintf("[%08x].mbm", $widgetdata->{'Uid'}));
        print "Generating: $mbm\n";
                    die "Failed to create MBM $mbm " if system("$cmd $self->{args}->{'verbose'} -in \"$icon\" -out $mbm -sizes ".ICON_SIZES) != 0;
    
        # Add the mbm to the list of files
        $self->addToRomList($drive, $mbm);
    
        # Create the INI file which defines the registry info
        my $ini = catfile($tempdir, 'reg.ini');
        $self->makeIni($widgetdata, $ini);
        unlink 'debug.ini'; copy($ini, 'debug.ini') if $debug;
        print "Generated INI file: $ini\n" if $self->{args}->{'verbose'};
    
        # Generate the registry files
        die "ERROR: Can't find WidgetRegFiles.exe command in PATH." if !($cmd = findCmd('WidgetRegFiles.exe'));
        die "Failed to generate registry files" if system("$cmd $ini") != 0;
        my ( $reg, $loc ) = ( catfile($dest, sprintf("%08x_reg.rsc", $widgetdata->{'Uid'})), catfile($dest, sprintf("%08x_loc.rsc", $widgetdata->{'Uid'})) );
        die "Failed to generate REG file: $!" if !-e $reg;
        $self->addToRomList($drive, $reg);
        die "Failed to generate LOC file: $!" if !-e $loc;
        if ($self->{'args'}->{'l10n'})
          {
              $self->addToRomList($drive, $loc);
          }
        else
          {
              $self->addToRomList($drive, $loc, 'localised');
          }
        }
        
    # Create install folder
    my $dir = $self->installDir($drive, $widgetdata->{'BundleIdentifier'});
    mkpath $dir;

    # Now copy the widget files to the right place
    print "Install Directory: $dir\n";
    foreach my $widgetfile ( @$extracted )
    {
      my ( $sourceFile, $destFile ) = ( catfile($tempdir, $widgetfile), catfile($dir, $widgetfile) );
      print "Copying $sourceFile to $destFile\n" if $self->{args}->{'debug'};

      # Create the directory if it doesn't exist already
      my $dir = dirname($destFile);
      if (!-d $dir)
        {
        mkpath ($dir) or die "Failed to create $dir $!";
        }
      unlink $destFile;
      if (!copy($sourceFile, $destFile))
        {
        warn "WARNING: Failed to copy $sourceFile to $destFile: $!";
        }
      #else
        {
        $self->addToRomList($drive, $destFile);
        }
    }

    # Copy the MBM file into the widget install directory
    # because native installation does and uses it after
    # installation to manage UID consistency.
    if( (!$isSharedLibrary) || ($isSharedLibrary && $isSharedIcon))
    {
        my $mbmName = sprintf("[%08x].mbm", $widgetdata->{'Uid'});
        my $destFile;
        if($w3c_widget)
        {
            my $dataDir;
            
            my $widget_uid;
      
			      if($non_nokia_widget)
			  		{
			  			$widget_uid = CWRT_WIDGET_UI_NON_NOKIA_UID;
			  		}
			  		else
			  		{
			      	$widget_uid = CWRT_WIDGET_UI_UID;
			      }
            
            # NOKIA:sharedlibrary check
            if($isSharedWidget)
            {
                $dataDir = fixFilename(catfile($self->destLocation($drive), 'private', sprintf("%08X", $widget_uid),"data","lib",$sharedFolderName));
            }
            else
            {
                #in case of WGT copy .mbm to \epoc32\winscw\C\private\200267c0\data\hash<BundleId>\
                $dataDir = fixFilename(catfile($self->destLocation($drive), 'private', sprintf("%08X", $widget_uid),"data", $hashval));
            }
            mkpath $dataDir;
            $destFile = catfile($dataDir,$mbmName);
        }
        else
        {
           $destFile = catfile($dir, $root, $mbmName);
        }
    		# Exclude securewidget from making a mbm file
			if (!$self->{'secure'}{lc $filename}){
            print "Copying $mbm to $destFile\n" if $self->{args}->{'debug'};
            copy $mbm, $destFile or die "Failed to copy $mbm to $destFile: $!";
            $self->addToRomList($drive, $destFile);
          	}
        }
        
    # Remember the data for the registry
    if( $w3c_widget )
      {
      push @installedCWRTProps, $widgetdata;
      }
    else
      {
	    if (!$self->{'secure'}{lc $filename}){
      		push @installedProps, $widgetdata;
      	}
      }

    if (!$debug)
      {
      # Perl v5.6 can't delete files with unicode in their name on Windows
      if ($] < 5.008 && $^O =~ /MSWin32/)
        {
        system("rmdir /s /q $tempdir");
        }
      else
        {
        rmtree $tempdir;
        }
      }
    #Generate the secsession for .wgt widgets
    if( $w3c_widget ) 
      {
      $self->addToRomList($drive, $self->makeSecSession($drive));
      }
  }

  my $cwrtdbPath = catfile($self->destLocation($drive), CWRT_WEBAPP_REGISTRY);
  $self->addToRomList($drive, $cwrtdbPath);
  
  # Generate the registry and IBY file
  $self->addToRomList($drive, $self->makeRegistry($drive, \@installedProps, 0));
  $self->addToRomList($drive, $self->makeRegistry($drive, \@installedCWRTProps, 1));
    

  print "\n\n%%%%%          WIDGET PRE-INSTALLATION completed for Drive $drive          %%%%% \n\n";
  }

sub un7zipWidget
  {
  my ( $self, $filename, $tempdir ) = @_;

  # Unzip the file
  die "Can't find 7z.exe tool on PATH." if !findCmd('7z.exe');
  die "Failed to extract widget contents using 7zip: $!" if (system("7z x -aoa -o$tempdir \"$filename\" >nul 2>&1") != 0);
  }

sub unzipWidget
  {
  my ( $self, $filename, $tempdir ) = @_;

  # Unzip the file
  die "Can't find unzip.exe tool on PATH." if !findCmd('unzip.exe');
  die "Failed to extract widget contents using zip: $!" if (system("unzip.exe \"$filename\" -d $tempdir >nul 2>&1") != 0);
  }

# Recursively get list of files in a folder
sub getFiles
  {
  my ( $self, $tempdir ) = @_;

  my $root = '.';
  my @extracted;
  my $size =0;
  
  my @dirs = '.';
  foreach my $dir ( @dirs )
    {
    opendir DIR, catfile($tempdir, $dir) or die "Failed to opendir $dir: $!";
    foreach ( grep !/^\.{1,2}$/, readdir DIR )
      {
      my $name = catfile($dir, $_);
      my $fullname = catfile($tempdir, $name);
      if (-d $fullname)
        {
        push @dirs, $name;
        }
      else
        {
        # Remember total size for later
        if (-e $fullname)
          {
          push @extracted, $name;
          print "Extracted: $name\n" if $self->{args}->{'debug'};
          $size += -s $fullname;

          # Get root
          if ($name =~ /info.plist$/i && $name =~ /^([^\/\\]+)[\/\\]/)
            {
            $root = $1;
            }
          }
        else
          {
          warn "WARNING: Failed to find extracted file $fullname";
          }
        }
      }
    closedir DIR;
    }

  return ( $root, \@extracted, $size );
  }

## see http://www.loc.gov/standards/iso639-2/php/code_list.php
## see http://www.loc.gov/standards/iso639-2/faq.html#2
sub getLocalisedStringByLangCode
  {
  my ( $self, $dir, $strName, $langCode ) = @_;
  my $localised;

  # Generate the name of the file containing localised strings for this language
  my $locfile = catfile($dir, "$langCode.lproj", "InfoPlist.strings");
  if (-e $locfile)
        {
    # Open the file
    print "Found $langCode language translations in $locfile\n" if $verbose;
    open LOC, $locfile or die "Failed to open $locfile: $!";

    # Get the byte order mark from the start of the file
    my $bom;
    $bom = unpack("S", $bom) if (read(LOC, $bom, 2) == 2);
    if ($bom)
      {
      if ($bom == 0xEFBB)
        {
        # Skip utf8 bom
        seek LOC, 3, 0;
        }
      elsif ($bom != 0xFFFE && $bom != 0xFEFF)
        {
        seek LOC, 0, 0;
        undef $bom;
        }
      }
    else
      {
      # go back to start of file if no bom
      seek LOC, 0, 0;
      undef $bom;
      }

    while(my $line = <LOC>)
      {
      # Do unicode conversion
      my $ustr;
      if ($bom)
        {
        $ustr = utf16($line);
        $ustr->byteswap if $bom != 0xFFFE;
        }
      else
        {
        $ustr = utf8($line);
        }

      # Find the string we're looking for
      if ($ustr->utf8 =~ /(?:^|\s)$strName\s*=\s*\"([^\"]*)\"/)
        {
        print "\t...$strName => $1\n" if $debug;
        $localised = utf8($1);
        }
      }
    close LOC;
    }
    return $localised;
  }

# Get localised version of strings if they exist
sub getLocalisedStrings
  {
  my ( $self, $dir, $strName ) = @_;
  return if (!$self->{'langmapping'});

  # Iterate through all the languages we know about
  my %result;
  for(my $i = 0; $i < scalar(@{ $self->{'langmapping'}->{LangID} }); $i++)
    {
    my ( $langid, $langname ) = ( $self->{'langmapping'}->{LangID}->[$i], $self->{'langmapping'}->{LangDir}->[$i] );

    my $localised = $self->getLocalisedStringByLangCode($dir, $strName, $langname);
    $result{$langid} = $localised if $localised;
    }

  return \%result if keys %result;
  }

# Find and execute a command
sub findCmd
  {
  my $cmd = shift;
  return fixFilename("./$cmd") if -e $cmd;

  # PATH separator differs on Windows and Linux
  my $sep = $^O =~ /MSWin32/ ? ';' : ':';

  # Search each entry in the PATH
  my @paths = split /$sep/, $ENV{PATH};
  push @paths, dirname($0);
  foreach my $path ( @paths )
    {
    my $fullcmd = fixFilename(catfile($path, $cmd));
    return $fullcmd if -e $fullcmd;
    }
  }

# Make INI file describing widget - this is passed to widgetregfiles.exe
sub makeIni
  {
  my ( $self, $data, $file ) = @_;
  open INI, ">$file" or die "Failed to open $file for writing: $!";
  binmode INI, ":utf8" if $] >= 5.008;

  # Get directory where mbm should go
  my $dir = $self->regFileName($data->{'DriveName'});

  print INI "[app_registration_info]\n";
  print INI sprintf("uid=%08x\n", $data->{'Uid'});
  print INI "app_file=$data->{'MainHTML'}\n";
  print INI "caption=$data->{'BundleDisplayName'}\n";
  print INI "drive_name=$data->{'DriveName'}\n";
  print INI "results_dir=$dir\n";
  
  if( $w3c_widget )
  {
    print INI "app_type=200267DC\n";
    print " WGT Widget:: app_type added to ini of widgetregfiles.exe \n" if $debug;
  }
  

  # Add language stuff if we have the mapping
  if ($data->{'LocBundleDisplayName'})
    {
    my @langList;
    foreach my $langid ( sort { $a <=> $b } keys %{ $data->{'LocBundleDisplayName'} } )
      {
      my $symid = sprintf("%02d", $langid);
      push @langList, $symid;
      print INI "caption$symid=", $data->{'LocBundleDisplayName'}->{$langid}->utf8, "\n";
      }
    print INI "languages=", join(' ', @langList), "\n";
    }

  close INI;
  convert2Unicode($file);
  }

 sub findfreeUid
  {
  my ( $self, $data ) = @_;
  my $appfile = lc $data->{'MainHTML'};
  my $uid;
  my $size;
    if($w3c_widget)     #CWRT Widget
    {
      # pick the next free CWRT Internal UID
      if(isInternal($data->{'DriveName'}))
      {
        print "\nInternal CWRT UID";
        $size = scalar @staticUidCwrtIntList;
        print " Static UID :: @staticUidCwrtIntList Length -- $size \n" if($size);
        for(my $i=0; $i<$size; $i++)
        {
		  #skip looping if freeUid found
          if( $self->{'freeuidcwrtint'} lt $staticUidCwrtIntList[$i] ) {last};
          
          if($self->{'freeuidcwrtint'} == $staticUidCwrtIntList[$i]) 
          { 
            $self->{'freeuidcwrtint'}++; 
          }
        }
        $uid = $self->{'freeuidcwrtint'}++;   # Assign and then set next free UID
      } 
      else
      {
        # pick the next free CWRT External UID
        print "\nExternal CWRT UID ";
        $size = scalar @staticUidCwrtExtList;
        print "Static UID :: @staticUidCwrtExtList Length -- $size \n";
        
        for(my $i=0; $i<$size; $i++)
        {
          if( $self->{'freeuidcwrtext'} lt $staticUidCwrtExtList[$i] ) {last};
          
          if($self->{'freeuidcwrtext'} == $staticUidCwrtExtList[$i]) 
          { 
            $self->{'freeuidcwrtext'}++; 
          }
        }
        $uid = $self->{'freeuidcwrtext'}++;   # Assign and then set next free UID
      }
    }
    else      #WRT widget
    {
      # pick the next free WRT Internal UID
      if(isInternal($data->{'DriveName'}))
      {
        # pick the next free CWRT Internal UID
        if(isInternal($data->{'DriveName'}))
        {
          print "\nInternal WRT UID ";
          $size = scalar @staticUidWrtIntList;
          print " STATIC UID :: @staticUidWrtIntList Length -- $size\n";
                 
          for(my $i=0; $i<$size; $i++)
          {
            if( $self->{'freeuidwrtint'} lt $staticUidWrtIntList[$i] ) {last};
            
            if($self->{'freeuidwrtint'} == $staticUidWrtIntList[$i]) 
            { 
              $self->{'freeuidwrtint'}++; 
            }
          }
          $uid = $self->{'freeuidwrtint'}++;   # Assign and then set next free UID
        }
      }
      else
      {
        # pick the next free WRT External UID
        print "\nExternal WRT UID ";
        $size = scalar @staticUidWrtExtList;
        print "STATIC UID :: @staticUidWrtExtList Length -- $size\n";
        
        for(my $i=0; $i<$size; $i++)
        {
          if( $self->{'freeuidwrtext'} lt $staticUidWrtExtList[$i] ) {last};
          
          if($self->{'freeuidwrtext'} == $staticUidWrtExtList[$i]) 
          { 
            $self->{'freeuidwrtext'}++; 
          }
        }
        $uid = $self->{'freeuidwrtext'}++;   # Assign and then set next free UID
      }
    }
  print sprintf("Generated UID: hex->0x%08X dec->$uid\n \n",$uid);
  return $uid;
  }

# Fix slash problems in a filename
sub fixFilename
  {
  my $filename = shift;
  $filename =~ s/([\\\/])[\\\/]/$1/g;
  return catfile(split(/[\\\/]/, $filename));
  }

# Get install location
sub destLocation
  {
  my ( $self, $drive ) = @_;
  my $letter = uc(substr($drive, 0, 1));
  
  # Was any destination location specified in the config file?
  if ($self->{destination} && $self->{destination}->{$letter})
    {
    return catfile($self->{'args'}->{'epocroot'}, $self->{destination}->{$letter});
    }
    
  # No destination specified - use emulator location
  return catfile($self->{'args'}->{'epocroot'}, $letter eq 'Z' ? ROM_DEST : sprintf(DRIVE_DEST, $letter));
  }
  
# Get the destination for REG/LOC/MBM file
sub regFileName
  {
  my ( $self, $drive, $filename ) = @_;
  my $result = catfile($self->destLocation($drive), DESTINATION, $filename);
  return fixFilename($result);
  }

# Widget install directory
sub installDir
  {
  my ( $self, $drive, $id ) = @_;
  my $result ;
  $hashval = hashpjw($id);
  if( $w3c_widget )
  {
  	my $widget_uid;
    if($non_nokia_widget)
	{
		$widget_uid = CWRT_WIDGET_UI_NON_NOKIA_UID;
	}
	else
	{
		$widget_uid = CWRT_WIDGET_UI_UID;
	}
    if($isSharedLibrary)
    {
    	$result = catfile($self->destLocation($drive), 'private', sprintf("%08X", $widget_uid),"widgets_21D_4C7", "lib",$sharedFolderName);
    }
    else
    {
        $result = catfile($self->destLocation($drive), 'private', sprintf("%08X", $widget_uid),"widgets_21D_4C7", $hashval);
    }
  }
  else
      {
	  	if ($isSecureWidget){
	   		print "Installing secure WGZ Widget\n";
	    	$result = catfile($self->destLocation($drive), 'private', sprintf("%08x", SWIDGET_UI_UID), $id);
	  	} else {
	   		print "Installing WGZ Widget\n";
        	$result = catfile($self->destLocation($drive), 'private', sprintf("%08x", WIDGET_UI_UID), $id);
	  	}
      }    
  return fixFilename($result);
  }

# Determines whether a drive should be considered internal or not
sub isInternal
  {
  my $drive = shift;
  die "Invalid drive format: $drive" if $drive !~ /^[a-zA-Z]:/;
  return 1 if $drive =~ /^[zcZC]/;
  }

# Parse these awful PLIST files
sub parsePList
  {
  my $file = shift;

  # Create parser object
  our ($key, $val, $plisthash ) = ('', '', {});
  my $parser = new XML::Parser;
  $parser->setHandlers('Doctype' => \&docT, 'Start' => \&startH, 'End' => \&endH, 'Char' => \&dataH);

  # Parse the file
  open XML, $file or die "Couldn't open $file";

  # Skip the UTF8 BOM - perl 5.6 can't handle it
  my $bom;
  read XML, $bom, 3;
  $bom = join('', map(sprintf('%X', $_), unpack("CCC", $bom)));
  print "Testing the following for BOM: $bom\n" if $debug;
  seek(XML, 0, 0) if $bom ne 'EFBBBF';

  $parser->parse(*XML);
  close XML;

  # Check required fields exist
  die "Widget MainHTML unknown" if !$plisthash->{'MainHTML'};
  die "Widget BundleIdentifier unknown" if !$plisthash->{'BundleIdentifier'};
  die "Widget BundleDisplayName unknown" if !$plisthash->{'BundleDisplayName'};

  # Return result
  return $plisthash;

  # Called on a start tag
  sub startH
    {
    my ($p, $el, %atts) = @_;
    undef $key if ($el =~ /^key$/i);
    $val = '';
    }

  # Receives document type
  sub docT
    {
    my ($expat, $name, $sysid, $pubid, $internal ) = @_;
    die "PLIST format looks wrong!" if lc($name) ne 'plist';
    $plisthash->{'NokiaWidget'} = ( $pubid =~ m[^-//Nokia//DTD PLIST]i ) ? 1 : 0;
    }

  # Receives character data
  sub dataH
    {
    my ($p, $s) = @_;
    $val .= $s;
    }

  # Called on an end tag
  sub endH
    {
    my ($p, $el) = @_;
    if ($el =~ /^key$/i)
      {
      $key = $val;
      }
    elsif ($key)
      {
      $val = 1 if $el =~ /^true$/i;
      $val = 0 if $el =~ /^false$/i;

      # Fix stuff so it's in the correct format
      $key =~ s/^CF//;
      $key = 'BundleIdentifier' if $key =~ /^Identifier$/i;
      $key = 'BundleDisplayName' if $key =~ /^DisplayName$/i;
      $key = 'BundleVersion' if $key =~ /^Version$/i;

      $plisthash->{$key} = $val;
      undef $key;
      }
    $val = ''
    }
  }


sub parseConfXml
  {
    my ( $file , $language ) = @_;

  our ($key, $val, $plisthash, $localizationValue,$localizationIconValue, $lang,$langIcon) = ('', '', {}, '','', {},{});
  our ($featureCount, $paramCount, $accessCount) = (1,1,1);
  our ($attributeMap, $featureMap, $featureParamMap, $accessMap)=('','','','');
  
  # Create parser object
  my $parser = new XML::Parser;
  $parser->setHandlers( 'Start' => \&startC, 'End' => \&endC, 'Char' => \&dataC);
   
  # Parse the file
  open XML,$file or die "Couldn't open $file";
  # Skip the UTF8 BOM - perl 5.6 can't handle it
  my $bom;
  read XML, $bom, 3;
  $bom = join('', map(sprintf('%X', $_), unpack("CCC", $bom)));
  print "Testing the following for BOM: $bom\n" if $debug;
  seek(XML, 0, 0) if $bom ne 'EFBBBF';
    $plisthash->{'NokiaWidget'} = 2 ;
    $plisthash->{'WidgetPackagingFormat'} = "w3c-partial-v1" ;
  
  $parser->parse(*XML);
  close XML;

    if( $language )
        {
         if($lang->{$language})
         { 
          $plisthash->{'BundleDisplayName'} = $lang->{$language};
         }
         if($langIcon->{$language})
         {
          $plisthash->{'IconPath'} = $langIcon->{$language};
         }
        }
  die "Widget BundleIdentifier unknown" if !$plisthash->{'BundleIdentifier'};
  die "Widget BundleDisplayName unknown" if !$plisthash->{'BundleDisplayName'};
  
   $attributeMap = $attributeMap.WIDGET_NAME.KEY_VALUE_SEPERATOR.$plisthash->{'BundleDisplayName'}.KEY_VALUE_PAIR_SEPERATOR;

   if($non_nokia_widget)
   {
       $attributeMap = $attributeMap.WIDGET_PROCESSUID.KEY_VALUE_SEPERATOR."200267D6".KEY_VALUE_PAIR_SEPERATOR;
   }
   else
   {
       $attributeMap = $attributeMap.WIDGET_PROCESSUID.KEY_VALUE_SEPERATOR."200267C0".KEY_VALUE_PAIR_SEPERATOR;
   }

    if($attributeMap)
    {      
        $plisthash->{'AttributeList'} = $attributeMap;
        print "\nAttributeList::$plisthash->{'AttributeList'}\n"
    }

  # Return result
  return $plisthash;

  # Called on a start tag
  sub startC
    {
    my ($p, $el, %atts) = @_;
    
    if($el eq "widget")
        {
         my $jilFeature = JIL_NS;
         if( lc($atts{"xmlns:JIL"})=~ m/$jilFeature/i || lc($atts{"xmlns:jil"})=~ m/$jilFeature/i)
         {
           $plisthash->{'WidgetPackagingFormat'} = "jil";
         }
         if ( $atts{"id"} )
             {
            $plisthash->{'BundleIdentifier'} = $atts{"id"};
            $attributeMap = $attributeMap.WIDGET_ID.KEY_VALUE_SEPERATOR.$atts{"id"}.KEY_VALUE_PAIR_SEPERATOR;
            
             }
         if ( $atts{"version"} )
             {
            $plisthash->{'BundleVersion'} = $atts{"version"};
            $attributeMap = $attributeMap.WIDGET_VERSION.KEY_VALUE_SEPERATOR.$atts{"version"}.KEY_VALUE_PAIR_SEPERATOR;
             }
         if ( $atts{"viewmodes"} && $atts{"viewmodes"} eq "all" )
             {
            $plisthash->{'MiniViewEnabled'} = 1;
             }
         $attributeMap = $attributeMap.WIDGET_HEIGHT.KEY_VALUE_SEPERATOR.$atts{"height"}.KEY_VALUE_PAIR_SEPERATOR;
         $attributeMap = $attributeMap.WIDGET_WIDTH.KEY_VALUE_SEPERATOR.$atts{"width"}.KEY_VALUE_PAIR_SEPERATOR;
        }
      elsif ($el eq "icon")
          {
           if ( $atts{"xml:lang"} )
             {
              $localizationIconValue = lc($atts{"xml:lang"}) ;
             }
           if ( $atts{"src"} )
             {
            $plisthash->{'IconPath'} = $atts{"src"};
                 }
          }
      elsif ($el eq "content")
          {
           $attributeMap = $attributeMap.WIDGET_CONTENT.KEY_VALUE_SEPERATOR.KEY_VALUE_PAIR_SEPERATOR;	
           if ( $atts{"src"} )
             {
            $plisthash->{'MainHTML'} = $atts{"src"};
            $attributeMap = $attributeMap.WIDGET_CONTENT.KEY_ATTR_SEPERATOR."src".KEY_VALUE_SEPERATOR.$atts{"src"}.KEY_VALUE_PAIR_SEPERATOR;
             }
          }
      elsif ($el eq "name")
          {
           if ( $atts{"xml:lang"} )
             {
              $localizationValue = lc($atts{"xml:lang"}) ;
             }
          }
      elsif ($el eq "feature")
          {
           $featureMap = WIDGET_FEATURE . $featureCount;
           $attributeMap = $attributeMap.$featureMap.KEY_VALUE_SEPERATOR.KEY_VALUE_PAIR_SEPERATOR;
           
           if ( $atts{"name"} )
             {
              $attributeMap = $attributeMap.$featureMap.KEY_ATTR_SEPERATOR."name".KEY_VALUE_SEPERATOR.$atts{"name"}.KEY_VALUE_PAIR_SEPERATOR;
              my $jilFeature = "http://jil.org/jil";
              if($atts{"name"}=~ m/^$jilFeature/i)
              {
                $plisthash->{'WidgetPackagingFormat'} = "jil";
              }
             }
         if ( $atts{"required"} )
             {
              $attributeMap = $attributeMap.$featureMap.KEY_ATTR_SEPERATOR."required".KEY_VALUE_SEPERATOR.$atts{"required"}.KEY_VALUE_PAIR_SEPERATOR;
             }
         }
       elsif($el eq "param")
          {
              $featureParamMap = $featureMap. WIDGET_FEATURE_PARAM . $paramCount;
              $attributeMap = $attributeMap.$featureParamMap.KEY_VALUE_SEPERATOR.KEY_VALUE_PAIR_SEPERATOR;
              if ($atts{"name"}) 
              {
                  $attributeMap = $attributeMap.$featureParamMap.KEY_ATTR_SEPERATOR."name".KEY_VALUE_SEPERATOR.$atts{"name"}.KEY_VALUE_PAIR_SEPERATOR;
              }
              if ($atts{"value"})
              {
                  $attributeMap = $attributeMap.$featureParamMap.KEY_ATTR_SEPERATOR."value".KEY_VALUE_SEPERATOR.$atts{"value"}.KEY_VALUE_PAIR_SEPERATOR;
              }
          }
       elsif ($el eq "access" || $el eq "jil:access" || $el eq "JIL:access")
          {
              $accessMap = WIDGET_ACCESS . $accessCount;
              $attributeMap = $attributeMap.$accessMap.KEY_VALUE_SEPERATOR.KEY_VALUE_PAIR_SEPERATOR;
           
              if ( $atts{"network"} )
             {
                $attributeMap = $attributeMap.$accessMap.KEY_ATTR_SEPERATOR."network".KEY_VALUE_SEPERATOR.$atts{"network"}.KEY_VALUE_PAIR_SEPERATOR;
             }
            if ( $atts{"remotescripts"} )
             {
                $attributeMap = $attributeMap.$accessMap.KEY_ATTR_SEPERATOR."remotescripts".KEY_VALUE_SEPERATOR.$atts{"remotescripts"}.KEY_VALUE_PAIR_SEPERATOR;
             }
             if ( $atts{"localfs"} )
             {
                $attributeMap = $attributeMap.$accessMap.KEY_ATTR_SEPERATOR."localfs".KEY_VALUE_SEPERATOR.$atts{"localfs"}.KEY_VALUE_PAIR_SEPERATOR;
             }
             if ( $atts{"origin"} )
             {
                $attributeMap = $attributeMap.$accessMap.KEY_ATTR_SEPERATOR."origin".KEY_VALUE_SEPERATOR.$atts{"origin"}.KEY_VALUE_PAIR_SEPERATOR;
             }
             if ( $atts{"subdomains"} )
             {
                $attributeMap = $attributeMap.$accessMap. KEY_ATTR_SEPERATOR."subdomains".KEY_VALUE_SEPERATOR.$atts{"subdomains"}.KEY_VALUE_PAIR_SEPERATOR;
             }
        }
        elsif ($el eq "NOKIA:sharedlibrary")
        {
            print " \n\n ^^^^^^^^^^^^^^^^^^^^^^^NOKIA:sharedlibrary ^^^^^^^^^^^^^^^^^^^^ \n\n";
            $isSharedLibrary = 1;
            $plisthash->{'WidgetPackagingFormat'} = "shared-library";
            $attributeMap = $attributeMap.WIDGET_NOKIA_SHAREDLIB.KEY_VALUE_SEPERATOR.KEY_VALUE_PAIR_SEPERATOR;
        }
     $val = '';    
     }
    
sub docC{}
# Receives character data
  sub dataC
    {
    my ($p, $s) = @_;
    $val .= $s;
    }

  # Called on an end tag
  sub endC
    {
    my ($p, $el) = @_;
    if ($el eq "name")
        {
       if( $localizationValue )
           {
            chomp($val);
            $lang->{$localizationValue} = $val;
            $localizationValue = '';
             }
         else
             {
              chomp($val);
              $plisthash->{'BundleDisplayName'} = $val;
             }   
      }
      elsif ($el eq "icon")
      {
        if( $localizationIconValue )
           {
            $langIcon->{$localizationIconValue} = $plisthash->{'IconPath'};
            print "\n %%%%%%%%%%%  $localizationIconValue  :: $plisthash->{'IconPath'}%%%%%%%%%%%%%\n";
            $localizationIconValue = '';
           }
      }
    elsif($el eq "feature")
      {
          $featureCount++;
          $paramCount = 0;
      }
    elsif($el eq "param")
      {
          $paramCount++;
      }
      elsif($el eq "access" || $el eq "jil:access")
      {
          $accessCount++;
      } 
      elsif ($el eq "NOKIA:folder")
        {
            chomp($val);
            $sharedFolderName = $val;
            $attributeMap = $attributeMap.WIDGET_NOKIA_SHAREDLIB_FOLDER.KEY_VALUE_SEPERATOR.$sharedFolderName.KEY_VALUE_PAIR_SEPERATOR;
        }
    elsif ($el eq "NOKIA:widget")
        {
            chomp($val);
            if( lc($val) eq "true" )
            {
                $isSharedWidget = 1;
                $plisthash->{'WidgetPackagingFormat'} = "w3c-partial-v1";
            }
            $attributeMap = $attributeMap.WIDGET_NOKIA_SHAREDLIB_WIDGET.KEY_VALUE_SEPERATOR.$val.KEY_VALUE_PAIR_SEPERATOR;
        }
    elsif ($el eq "NOKIA:icon")
        {
            chomp($val);
            if( lc($val) eq "true" )
            {
                $isSharedIcon = 1;
            }
            $attributeMap = $attributeMap.WIDGET_NOKIA_SHAREDLIB_ICON.KEY_VALUE_SEPERATOR.$val.KEY_VALUE_PAIR_SEPERATOR;
        }
    $val = ''
    }

  }


# Stores the details of files to be added to "rom"
sub addToRomList
  {
  my ( $self, $drive, $file, $localised ) = @_;
  $file = fixFilename($file);

  # All files should be under epoc32 somewhere - need to drop a bit of the path for the rom destination
  my $localpath = $self->destLocation($drive);

  my $dest = fixFilename($file);
  $dest =~ s/^\Q$localpath\E//i;

  # Add the file to the list for the rom
  # It may be localised - in which it'll be put in a different IBY file
  $localised = $localised ? '_rsc' : '';
  $self->{"installedFiles${localised}"}->{$drive}->{$file} = $dest;
  }

# Make the IBY file
sub makeIBY
  {
  my ( $self, $drive, $localised ) = @_;

  # Generate the file name for the IBY file
  $localised = $localised ? '_rsc' : '';
  my $name = $drive =~ /^[zZ]/ ? "preinstalledwidgets${localised}.iby" : sprintf("preinstalledwidgets_drive%s${localised}.iby", substr($drive, 0, 1));
  my $iby = fixFilename(catfile($self->{'args'}->{'epocroot'}, 'epoc32', 'rom', 'include', $name));
  print "Generating: $iby\n";

  mkpath dirname($iby);
  open IBY, ">$iby" or die "Failed to open $iby for writing: $!";
  $name =~ s/\./_/g; $name = uc($name);
  print IBY "// GENERATED FILE: EDIT WITH CARE\n\#ifndef __${name}__\n\#define __${name}__\n\n";
  foreach my $file ( sort keys %{ $self->{"installedFiles${localised}"}->{$drive} } )
    {
    my $dest = $self->{"installedFiles${localised}"}->{$drive}->{$file};

    # Quote filenames as they may contain spaces!
    print IBY "data=\"$file\"\t\"$dest\"\n";
    }
  print IBY "\#endif\n";
  close IBY;
  }

# Unregister (with Apparc) existing Widgets
sub unregisterWidgets
{
  my ( $self, $drive ) = @_;
    
    my $registry = fixFilename(catfile($self->destLocation($drive), WIDGET_REGISTRY));
  # If the WRT registry already exists, remove apparc registry info for those widgets
  # This should avoid problems with unregistered widget icons in the emulator?
    if (-e $registry)
    {
        print("\n     UNREGISTERING WGZ WIDGETS       \n");

      my $ref = XMLin($registry, 'forcearray' => [ 'entry' ], 'keyattr' => { 'prop' => 'content' } );
    foreach my $entry ( @{ $ref->{entry} } )
      {
      my $uid = $entry->{prop}->{Uid}->{val}->{content};

      print "Unregistering existing Widget: $entry->{prop}->{BundleIdentifier}->{val}->{content}\n" if $verbose;
      my $dest = $self->regFileName($drive);
      my $mbm = catfile($dest, sprintf("[%08x].mbm", $uid));
      my ( $reg, $loc ) = ( catfile($dest, sprintf("%08x_reg.rsc", $uid)), catfile($dest, sprintf("%08x_loc.rsc", $uid)) );
      unlink $mbm, $reg, $loc;
    
      # We also have to delete the widget directory otherwise it'll be re-registered
      my $id = $entry->{prop}->{BundleIdentifier}->{val}->{content};
      $w3c_widget = 0;
      my $dir = $self->installDir($drive, $id);
      rmtree $dir;
      }
    }
    
  $registry = fixFilename(catfile($self->destLocation($drive), CWRT_WIDGET_REGISTRY));

  # If the CWRT registry already exists, remove apparc registry info for those widgets
  # This should avoid problems with unregistered widget icons in the emulator?
  if (-e $registry)
    {
        print("\n     UNREGISTERING WGT WIDGETS       \n");

          my $ref = XMLin($registry, 'forcearray' => [ 'entry' ], 'keyattr' => { 'prop' => 'content' } );
        foreach my $entry ( @{ $ref->{entry} } )
      {
          my $uid = $entry->{prop}->{Uid}->{val}->{content};
    
          print "Unregistering existing Widget: $entry->{prop}->{BundleIdentifier}->{val}->{content}\n" if $verbose;
          my $dest = $self->regFileName($drive);
            my $mbm = catfile($dest, sprintf("[%08x].mbm", $uid));
          my ( $reg, $loc ) = ( catfile($dest, sprintf("%08x_reg.rsc", $uid)), catfile($dest, sprintf("%08x_loc.rsc", $uid)) );
          unlink $mbm, $reg, $loc;
       
          # We also have to delete the widget directory otherwise it'll be re-registered
          my $id = $entry->{prop}->{BundleIdentifier}->{val}->{content};
          print "Unregistering $id\n";
          my $basepath = $entry->{prop}->{BasePath}->{val}->{content};
          $w3c_widget = 1;
          my $sharedLib = "lib";          #BasePath will have lib only if the widget is shared Library
          
          if($basepath =~ m/$sharedLib/)
          {
              $isSharedLibrary = 1;
          }
          
          if($basepath =~ m/\\200267d6\\/i)
          {
          	$non_nokia_widget = 1;	
          }
           #sharedFolderName TBD
          my $dir = $self->installDir($drive, $id);
          rmtree $dir;

          $dir =~ s/widgets_21D_4C7/data/;
          rmtree $dir;
        }
    }
    #delete CWRT webapp DB if exists
    my $cwrtdbPath = catfile($self->destLocation($drive), CWRT_WEBAPP_REGISTRY);
    if($cwrtdbPath)
    {
    	print "Deleting CWRT_WEBAPP_REGISTRY \n";
    	rmtree $cwrtdbPath;
    }
  }

# Make the registry
sub makeRegistry
  {
  my ($self, $drive, $installed, $w3c) = @_;
  
  my ($registry);
  if($w3c)
    {
    $registry = fixFilename(catfile($self->destLocation($drive), CWRT_WIDGET_REGISTRY));
    }
  else
    {
    $registry = fixFilename(catfile($self->destLocation($drive), WIDGET_REGISTRY));
    }
    
  print "\nGenerating: $registry\n";

  # Write the file
  mkpath dirname($registry);
  open OUT, ">$registry" or die "Failed to open WidgetEntryStore.xml: $!";

  print OUT "<?xml version=\"1.0\" encoding=\"UTF-16\" standalone=\"yes\" ?>\n<widgetregistry>\n";
  binmode OUT, ":utf8" if $] >= 5.008;
  foreach my $pList ( @$installed )
    {
    $self->dumpPList(\*OUT, $pList, $w3c);
    }
  print OUT "</widgetregistry>\n";
  close OUT;

  # Convert the file to unicode
  convert2Unicode($registry);

  # Return the generated file
  return $registry;
  }

# Converts a file to Unicode
sub convert2Unicode
  {
  my $file = shift;

  my @lines;
  open IN, $file or die "Failed to open $file: $!";
  binmode IN;
  while(<IN>)
    {
    my $u = utf8($_);
    $u->byteswap;
    push @lines, $u->utf16;
    }
  close IN;

  open OUT, ">$file" or die "Failed to open $file for writing: $!";
  binmode OUT;
  print OUT pack("CC", 0xff, 0xfe);
  print OUT @lines;
  close OUT;
  }

sub hashpjw {
  my $s = shift;
  my $hashval = 0;
  my $g;

  for ( split //, $s ) {
    $hashval = ( $hashval << 4 ) + ord $_; 
    
    if ($g = $hashval & 0xf0000000) {
      $hashval ^= $g >> 23;
    }
    $hashval &= ~$g;
  }
  #print "$hashval \n";
  return $hashval;
} 

# Dumps a single PList hash object
sub dumpPList
  {
  my ($self, $fh, $data, $w3c) = @_;
  my @regProperties = (
    [ 'PropertyListVersion', 'int' ],
    [ 'BundleIdentifier', 'string' ],
    [ 'BundleName', 'string' ],
    [ 'BundleDisplayName', 'string' ],
    [ 'MainHTML', 'string' ],
    [ 'BundleVersion', 'string' ],
 #  [ 'Height', 'int' ],
 #  [ 'Width', 'int' ],
    [ 'AllowNetworkAccess', 'int' ],
    [ 'DriveName', 'string' ],
    [ 'BasePath', 'string' ],
    [ 'IconPath', 'string' ],
    [ 'FileSize', 'int' ],
    [ 'Uid', 'int' ],
    [ 'NokiaWidget', 'int' ],
    [ 'MiniViewEnabled', 'int' ],
    [ 'ProcessUid', 'int' ],
    [ 'MimeType', 'string'],
    [ 'WidgetPackagingFormat', 'string'],
    [ 'DBIconPath', 'string'],
    [ 'AttributeList', 'string'],
    [ 'BlanketPermissionGranted', 'int' ],
    [ 'PreInstalled', 'int' ],
  );
    
  print $fh "<entry>\n";
  my $encodeddata = {};
  foreach my $prop ( @regProperties )
    {
    my ( $key, $type ) = @$prop;
    if($key ne "DBIconPath" && $key ne "WidgetPackagingFormat" && $key ne "AttributeList" && $key ne "BlanketPermissionGranted" && $key ne "PreInstalled")
    {
        print $fh "<prop>$key<val>$data->{$key}<type>$type</type></val></prop>\n" if defined $data->{$key};
    }
    
    if( $w3c )
      {
      $encodeddata->{$key} = encodeChar($data->{$key}) if defined $data->{$key};
      }
    else
    {
    	if($key eq "BlanketPermissionGranted" || $key eq "PreInstalled")
    	{
    	 print $fh "<prop>$key<val>$data->{$key}<type>$type</type></val></prop>\n" if defined $data->{$key};
    	}
    }
    }
  print $fh "</entry>\n";
  if( $w3c )
    {
  my $dbPath = fixFilename(catfile($self->destLocation('C'), CWRT_WEBAPP_REGISTRY));
    mkpath dirname($dbPath);
    die "ERROR: Can't find CWRTWebAppRegistry.exe in PATH" if !(my $cmd = findCmd('CWRTWebAppRegistry.exe'));
    my $regCmd;
    
    if($encodeddata->{'AttributeList'})
    {
        print "\nAttributeList argument sent to DB\n";
        $regCmd = "$cmd $dbPath $encodeddata->{'BundleIdentifier'} $encodeddata->{'Uid'} $encodeddata->{'BundleDisplayName'} $encodeddata->{'BasePath'} $encodeddata->{'DBIconPath'} $encodeddata->{'WidgetPackagingFormat'} $encodeddata->{'MainHTML'} $encodeddata->{'AttributeList'}";
    }
    else
   {
        print "\nAttributeList argument not sent to DB\n";
        $regCmd = "$cmd $dbPath $encodeddata->{'BundleIdentifier'} $encodeddata->{'Uid'} $encodeddata->{'BundleDisplayName'} $encodeddata->{'BasePath'} $encodeddata->{'DBIconPath'} $encodeddata->{'WidgetPackagingFormat'} $encodeddata->{'MainHTML'}";
    }
    print "\n regCmd : $regCmd \n\n";
    system($regCmd);
    }
  }

#encode the space character
sub encodeChar  
  {
    my  ($encoded) = @_;

    $encoded =~ s/%/%10/g;
    $encoded =~ s/\s/%40/g;
    $encoded =~ s/\'/%apos/g;   
    $encoded =~ s/&/%amp/g;
    $encoded =~ s/</%lt/g;
    $encoded =~ s/>/%gt/g;
    $encoded =~ s/\"/%quot/g;
    return $encoded;
  }
  
  
# Make secssion
sub makeSecSession
    {
  my ($self, $drive) = @_;
  my $secSession;
  my $widget_uid;
  if($non_nokia_widget)
	{
		$widget_uid = CWRT_WIDGET_UI_NON_NOKIA_UID;
	}
	else
	{
  	$widget_uid = CWRT_WIDGET_UI_UID;
  }

  if($isSharedLibrary)
  {
      $secSession = fixFilename(catfile($self->destLocation($drive), 'private', sprintf("%08X", $widget_uid),"data","lib",$sharedFolderName,"secsession"));
  }
  else
  {
      $secSession = fixFilename(catfile($self->destLocation($drive), 'private', sprintf("%08X", $widget_uid),"data", $hashval,"secsession"));
  }
  print "\nGenerating: $secSession\n\n";
  
  # Write the file
  mkpath dirname($secSession);
  open OUT, ">$secSession" or die "Failed to open SecSession.xml: $!";

  print OUT "<?xml version=\"1.0\" encoding=\"ISO-8859-1\" ?>\n<accesspolicy>\n";
  if($non_nokia_widget)
  {
  	print OUT "<domain name=\"Operator\">\n";
  }
  else
  {
  	print OUT "<domain name=\"TrustedWidgets\">\n";
  }
  
  if(CWRT_ACCESS_POLICY_PATH) {
      my $accesspolicypath = findCmd(CWRT_ACCESS_POLICY_PATH);   
        # Copy Secsession capabilities from browser_access_policy.xml if it exists
      if (-e $accesspolicypath) {
          print "Browser Access Policy File exists :: ",$accesspolicypath,"\n" ;
          my $accesspolicy = XMLin($accesspolicypath, keyattr => {domain => 'name'}, forcearray =>['domain'] );
            my $domainName;
            
            if($non_nokia_widget)
            {
            	$domainName = $accesspolicy->{domain}->{Operator};
            }
            else
            {
            	$domainName = $accesspolicy->{domain}->{TrustedWidgets};
            }
          
          my $xml = XMLout($domainName, keeproot => 1);
          print OUT $xml;
      }
      #browser_access_policy.xml does not exist in the path
      else {      
          print "\n Browser Access policy file '$accesspolicypath' does not exist in the given path\n";
          if(!$non_nokia_widget)
          {
          	print OUT "   <capability name=\"Download\"/>\n   <capability name=\"ApplicationManagement\"/>\n   <capability name=\"WebAppUpdate\"/>\n   <capability name=\"DeviceConfiguration\"/>\n   <capability name=\"NokiaAccount\"/>\n   <capability name=\"ConnectionManagement\"/>\n   <capability name=\"ApplicationManagement.Launch\"/>\n   <capability name=\"SecureStorage\"/>\n   <capability name=\"EventsAndMessaging\"/>\n   <capability name=\"Vibra\"/>\n   <capability name=\"RuntimeInfo\"/>\n   <capability name=\"OviMessagingBus\"/>\n   <capability name=\"NativeUpdate\"/>\n   <capability name=\"LocalConnectivity\"/>\n   <capability name=\"Network\"/>\n   <capability name=\"Cryptographic\"/>\n   <capability name=\"pim.*\"/>\n   <capability name=\"devicestatus.*\"/>\n   <capability name=\"message.*\"/>\n   <capability name=\"sensor.*\"/>\n   <capability name=\"landmark.*\"/>\n   <capability name=\"camera.*\"/>\n   <capability name=\"commlog.*\"/>\n   <capability name=\"media.*\"/>\n   <capability name=\"io.file.*\"/>\n   <capability name=\"player.*\"/>\n   <capability name=\"location.position\"/>\n   <capability name=\"telephony.voicecall\"/>\n   <capability name=\"NokiaAdEnabler\"/>\n";
          }
        }
    }
    #Access policy path not defined
  else {
      print "\n Browser Access policy path not defined \n";
      if(!$non_nokia_widget)
      {
      	print OUT "   <capability name=\"Download\"/>\n   <capability name=\"ApplicationManagement\"/>\n   <capability name=\"WebAppUpdate\"/>\n   <capability name=\"DeviceConfiguration\"/>\n   <capability name=\"NokiaAccount\"/>\n   <capability name=\"ConnectionManagement\"/>\n   <capability name=\"ApplicationManagement.Launch\"/>\n   <capability name=\"SecureStorage\"/>\n   <capability name=\"EventsAndMessaging\"/>\n   <capability name=\"Vibra\"/>\n   <capability name=\"RuntimeInfo\"/>\n   <capability name=\"OviMessagingBus\"/>\n   <capability name=\"NativeUpdate\"/>\n   <capability name=\"LocalConnectivity\"/>\n   <capability name=\"Network\"/>\n   <capability name=\"Cryptographic\"/>\n   <capability name=\"pim.*\"/>\n   <capability name=\"devicestatus.*\"/>\n   <capability name=\"message.*\"/>\n   <capability name=\"sensor.*\"/>\n   <capability name=\"landmark.*\"/>\n   <capability name=\"camera.*\"/>\n   <capability name=\"commlog.*\"/>\n   <capability name=\"media.*\"/>\n   <capability name=\"io.file.*\"/>\n   <capability name=\"player.*\"/>\n   <capability name=\"location.position\"/>\n   <capability name=\"telephony.voicecall\"/>\n   <capability name=\"NokiaAdEnabler\"/>\n";
      }
  }
   
    print OUT "</domain>\n";
    print OUT "</accesspolicy>\n";
    close OUT;

  # Return the generated file
  return $secSession;
  }
__END__

=head1 NAME

installwidgets.pl - A script for generating all the files needed to install Widgets

=head1 SYNOPSIS

installwidgets.pl [-h] [-ver] [-v] [-debug] [-e <dir>] [-l <lang_code|lproj.xml>] config.ini

 Options:
   -help|h                        Show this help
   -version|ver                   Show version number
   -verbose|v                     Show verbose output
   -debug                         Show debug output
   -epocroot|e                    Override value of EPOCROOT
   -localization|l                lproj_dir

A script for generating all the files needed to preinstall Widgets.

 Example:
   perl installwidgets.pl -l fr config.ini       Install widgets listed in config.ini using French localization

 Author:
   peter.harper@sosco.com

=head1 DESCRIPTION

This tool can be used to pre-generate all the files needed to install Widgets. The tool and its dependencies can be placed anywhere on your PATH.
It generates the results in the epoc32 folder - in the appropriate locations for the emulator.
It finds the epoc32 folder using the EPOCROOT environment variable which can be overridden via the -e command line option.

=head2 CONFIG FILE

The preferred way to run the tool is via a configuration INI file.
You can list the widgets to install on each drive. You can specify the exact location of the Widget, otherwise it will try and find the Widget via EPOCROOT.

You can specify whether a widget is intended for the homescreen by adding the text [HomeScreen] after the filename
This will set the BlanketPermissionGranted attribute in the registry.
Widgets intended for the homescreen must have the MiniViewEnabled attribute set in its PLIST file otherwise an error is generated.

    # Widgets to be pre-installed for the ROM
    [drive-z]
    \somepath\foo.wgz
    \somepath\bar.wgz

    # Widgets for the internal disk
    [drive-c]
    \somepath\widget1.wdgt.zip [HomeScreen]

    # Widgets for the removable disk
    [drive-e]
    \somepath\widget2.wdgt.zip

    # Commands to run at the end
    [run-commands]
    dostuff.pl
    domorestuff.exe

=head2 DEPENDENCIES

The tool has some dependencies which must exist for it to work.

=over

=item 1

png2mbm.pl - A script to generate an MBM file from a PNG

=item 2

WidgetRegFiles.exe - an EXE which can generate Symbian REG and LOC files for registering non-native Widget apps.
This tool is built with "SymPort" a native tools port of basic Symbian OS services.

=item 3

7z/unzip - For extracting files from the Widget archive.
7Zip will be used in preference to unzip if it's found on your path because it handles Unicode a better.

=item 4

GD.pm - Perl support for the GD graphics library for PNG support, see http://www.libgd.org .

=back

=head3 INSTALLING GD

You can install GD automatically with a simple command - however the command you need to use differs depending on the version of Perl you have installed.
At the time of writing Symbian requires Perl version 5.6 - although in my experience Perl 5.8 works okay. To find out which version of Perl you have type "perl -v" on the command line.

To install the GD library:

=over

=item *

For Perl v5.6: "ppm install http://theoryx5.uwinnipeg.ca/ppmpackages/GD.ppd "

=item *

For Perl v5.8: "ppm install http://theoryx5.uwinnipeg.ca/ppms/GD.ppd "

=back

=head2 WIDGET INSTALL PROCESS

Here's a detailed breakdown of what the script does.

=over

=item 1

It gets the lists of Widgets from the config.ini file passed on the command line.
This process is repeated for all Widgets and all drives listed in the config file.

=item 2

Any existing Widgets listed in "private\10282f06\WidgetEntryStore.xml" are deleted from the epoc32 tree.
This ensures that there are no problems when testing Widgets in the emulator.

=item 3

All the compressed files in the Widget are extracted to a temporary folder.

=item 4

The details for the Widget are loaded from its "Info.plist" file.

=item 5

A UID is chosen for the widget. This differs depending on whether installation is for an internal drive (z: or c:) or an external drive (e: etc).

=item 5

A Symbian MBM file is generated from the "Icon.png" file supplied by the Widgets.
Three different sized icons are generated "88x88", "32x32" and "24x24".
The MBM file is placed in "private/10003a3f/import/apps/NonNative/Resource/[<UID>].mbm".

=item 6

"WidgetRegFiles.exe" is executed to generate REG and LOC resource files used to register the Widget as an app in Symbian OS.
These files are placed in "private/10003a3f/import/apps/NonNative/Resource".

=item 7

All the widgets files are copied to a folder under "private\10282822".
The Widget's bundle identifier is used to create a unique folder under here for the Widget.

=item 8

The Widget registry is generated in "private\10282f06\WidgetEntryStore.xml"

=item 9

If Widgets are being preinstalled for ROM an IBY file is created in "epoc32\rom\include\preinstalledwidgets.iby".
A separate IBY file is generated for the localised parts of a Widget "epoc32\rom\include\preinstalledwidgets_rsc.iby".
Separate IBY files (per drive) are generated for Widgets preinstalled to UDA, e.g. preinstalledwidgets_driveC.iby and preinstalledwidgets_driveC_rsc.iby.
These IBY files can be used to add all the Widgets to ROM, ROFS or UDA.

=back

=head3 INSTALLING ON HARDWARE USING iMaker

=over

=item 1

Create the following folder structure at the root level.

X:\variants\content

=item 2

Copy the files specified in the generated ibys (preinstalledwidgets_driveC.iby and preinstalledwidgets_driveC_rsc.iby) to X:\variants\content. Preserve the dir structure. (Note, this step will be automated in the future)

For example if you want the following file on UDA (User Disk Area, C drive on phone) at the following location C:\private\10282f06\WidgetEntryStore.xml

Drop the file under X:\variants\content\private\10282f06\WidgetEntryStore.xml 

=item 3

Run the foll command to generate UDA

B<Gadget:>
X:\epoc32\tools>imaker -f /epoc32/rom/s60_makefiles/image_conf_sp_rnd_gadget.mk VARIANT_DIR=/variants variantuda

B<Tube:>
Y:\epoc32\tools>imaker -f /epoc32/rom/config/ncp52/tube/image_conf_tube_ui.mk VARIANT_DIR=/variants variantuda 

=item 4

Flash the fpsx file generated under X:\epoc32\rombuild\gadget\uda for Gadget and Y:\epoc32\rombuild\tube\uda for Tube to your device.

Note: More info on iMaker tool at: L<http://configurationtools.nmp.nokia.com/imaker/wiki/iMakerUserGuide>

=back

=head3 LOCALISATION

Widget handles localization by providing localized resources in various language project directories(lproj_dir), one level deep than the root directory. In order to specify a language variant for pre-installing widget, you need to provide the language project directory name, e.g. 'en' for english, 'fr' for French.

A list of Nokia supported languages can be found in Widget_lproj.xml or at L<http://wiki.forum.nokia.com/index.php/Web_Runtime_localisation_support>. If the widget does not provide the localized resource for the variant you specified, the default resources in widget's home directory will be used instead. 

=head3 NOTES

=over

=item 1

The location of the private folder is in the appropriate place for the files to appear in the emulator.
This is different depending on the intended destination drive (see -dd command line option) for the Widget.
e.g. "epoc32/release/winscw/udeb/z/", "epoc32/winscw/c" or "epoc32/winscw/e"

=item 2

Files are extracted to epoc32 on the current drive relative to the EPOCROOT environment variable or the value given for -epocroot (-e) on the command line.

=item 3

A different IBY file is generated for each drive.

=over

=item *

Z: - \epoc32\rom\include\preinstalledwidgets.iby

=item *

C: - \epoc32\rom\include\preinstalledwidgets_driveC.iby

=item *

E: - \epoc32\rom\include\preinstalledwidgets_driveE.iby

=back

There are separate resource files for localised resources e.g. preinstalledwidgets_rsc.iby.

=cut
