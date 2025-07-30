package ar.uba.dc;

import ar.uba.dc.EPA.SBEPA;
import ar.uba.dc.config.Config;

import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.Duration;
import java.time.LocalDateTime;
import java.time.ZoneId;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;

public class MainMODELS {

    // The code take the alloy model in subfolder_* and never modify that file. It will copy that model in the parent
    // folder and there will modify it.
    // It will save times in root_folder.
    // It is mandatory to have the alloy model file (.als) and a config file (.ini) in the same folder.
    // The config file must have the same name that the alloy file but ending in "Config.ini".


    public static void main(String[] args)  {


        if (args.length == 0) {
            System.err.println("Please provide at least one file or directory path as argument.");
            System.exit(1);
            return;
        }

        List<String> subjects_to_generate_abstraction = getFilesToAnalyze(args);

        if (subjects_to_generate_abstraction.isEmpty()) {
            System.err.println("No .als files found in the provided paths.");
            System.exit(1);
            return;
        }

        // Checks if any path is wrong or if the config file does not exist
        // If any path is wrong, it will throw an exception and the program will exit.
        checkIfSubjectsExists(subjects_to_generate_abstraction);

        // Print the subjects to generate abstraction
        System.out.println("=========================================");
        System.out.println("Subjects to generate abstraction:");
        System.out.println("=========================================");
        subjects_to_generate_abstraction.forEach(System.out::println);
        System.out.println("=========================================");


        try {
            LocalDateTime init = LocalDateTime.now();
            List<String> times = new ArrayList<>();
            times.add("Subject,EPA (secs), BEPA (secs), SBEPA");
            //For each subject, generate EPA/BEPA/SEPA
            for (String original_file_path : subjects_to_generate_abstraction) {
                System.out.println("\nSTARTING WITH FILE: " + original_file_path);
                if (!Config.OVERWRITE_SUBJECTS && already_processed(original_file_path)) {
                    System.out.println("Subject " + original_file_path + " already processed. SKIPPED");
                    continue;
                }
                SBEPA sbepa = new SBEPA(original_file_path);
                sbepa.buildFullEPA();

                Path path = Paths.get(original_file_path);
                String line = path.getFileName().toString().replace(".als", "");
                line += "," + sbepa.TIMES[0] + "," + sbepa.TIMES[1] + "," + sbepa.TIMES[2];
                times.add(line);
            }

            writeTimes(times);

            LocalDateTime end = LocalDateTime.now();
            System.out.println("Total time all subjects (seconds): " + Duration.between(init, end).getSeconds());
        } catch (InterruptedException e) {
            System.out.println("InterruptedException: " + e.getMessage());
            e.printStackTrace();
            throw new RuntimeException(e);
        } catch (ExecutionException e) {
            System.out.println("ExecutionException: " + e.getMessage());
            e.printStackTrace();
            throw new RuntimeException(e);
        } catch (Exception e) {
            System.out.println("Exception: " + e.getMessage());
            e.printStackTrace();
            throw new RuntimeException(e);
        } finally {
            System.out.println("End.");
            System.exit(0);
        }
    }

    private static boolean already_processed(String originalFilePath) {
        Path path = Paths.get(originalFilePath);
        Path parentParentDir = path.getParent().getParent();
        String subjectName = path.getFileName().toString().replace(".als", "");
        Path subjectDir = Paths.get(parentParentDir.toString(), subjectName);
        return Files.exists(subjectDir) && Files.isDirectory(subjectDir);
    }

    private static List<String> getFilesToAnalyze(String[] args) {
        List<String> alsFiles = new ArrayList<>();
        for (String arg : args)
        {
            File file = new File(arg);
            if (!file.exists())
            {
                System.err.println("Path does not exist: " + arg);
                System.exit(1);
            }
            if (file.isFile() && !arg.endsWith(".als"))
            {
                System.err.println("Files must be .als files: " + arg);
                System.exit(1);
            }
            if (file.isFile() && arg.endsWith(".als"))
            {
                alsFiles.add(file.getAbsolutePath());
            } else if (file.isDirectory())
            {
                File[] files = file.listFiles((dir, name) -> name.endsWith(".als"));
                if (files != null)
                {
                    for (File f : files) {
                        alsFiles.add(f.getAbsolutePath());
                    }
                }
            }
        }
        return alsFiles;
    }

    private static void checkIfSubjectsExists(List<String> alsFiles) {
        alsFiles.forEach(e -> {
            if (!new File(e).exists()) {
                throw new IllegalArgumentException("File does not exists: " + e);
            }
        });
        alsFiles.forEach(e -> {
            Path path = Paths.get(e);
            String configFileName = path.getFileName().toString().replaceFirst("\\.als$", "Config.ini");
            File configFile = path.getParent() != null
                    ? new File(path.getParent().toString(), configFileName)
                    : new File(configFileName);
            if (!configFile.exists()) {
                throw new IllegalArgumentException("Config file does not exist: " + configFile.getAbsolutePath());
            }
        });
    }

    private static void writeTimes(List<String> tiempos) {
        try {
            String date_now_format = LocalDateTime.now(ZoneId.systemDefault()).format(DateTimeFormatter.ofPattern("dd_MM_yyyy_HH_mm"));
            String statistics = Paths.get(Config.OUTPUT_STATISTICS_PATH, date_now_format + "_statistics.csv").toString();
            // Ensure the output directory exists
            File statisticsFile = new File(statistics);
            File parentDir = statisticsFile.getParentFile();
            if (parentDir != null && !parentDir.exists()) {
                parentDir.mkdirs();
            }
            FileWriter file = new FileWriter(statistics);
            PrintWriter pw = new PrintWriter(file);
            for (String t : tiempos) {
                pw.println(t);
            }
            file.close();
            tiempos.forEach(System.out::println);
        } catch (Exception e) {
            System.err.println("Error writting Times: " + e.getMessage());
            e.printStackTrace();
        }
    }


}