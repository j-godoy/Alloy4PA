## Alloy for Predicate Abstractions (Alloy4PA)

This tool automatically analyzes Alloy models to generate modal abstractions.
The only required input is an Alloy model (`.als` file) that encodes the corresponding Solidity smart contract (or another other artifact). For correct operation, each public method in the Solidity contract must be represented in the Alloy model as a predicate with the name `met_F`, where `F` is the name of the public Solidity function.

The tool produces many output files, where the most important is a `.dot` file that describe the modal transition system for the analyzed subject.

## How to run

#### Clone the repository

```sh
git clone https://github.com/j-godoy/Alloy4PA.gitcd Alloy4PA
```

### Option 1: Use the precompiled JAR

**Prerequisites:**  

* Ensure Java 18 or newer is installed.
* Set the `JAVA_HOME` environment variable.

To check if Java is installed, run:

```sh
java -version
```

To verify `JAVA_HOME` is set (on Unix-like systems):

```sh
echo $JAVA_HOME
```

If not set, you can set it temporarily with:

```sh
export JAVA_HOME=$(readlink -f $(which java) | sed 's:/bin/java::')
```

---

To run the tool, use:

```sh
java -jar Alloy4PA/target/Alloy4PA-1.0.0-fat-jar-with-dependencies.jar <path1> <path2> ...
```

For example, to analyze one of the provided Alloy models, run:

```sh
java -jar Alloy4PA/target/Alloy4PA-1.0.0-fat-jar-with-dependencies.jar examples/Benchmarks/B1/alloy_models/BasicProvenance.als
```

This will generate output files in the `examples/Benchmarks/B1/BasicProvenance/` directory.

To visualize the modal transition system (MTS) for this subject, open the file `examples/Benchmarks/B1/BasicProvenance/BasicProvenanceforked_arrows.dot`. You can view the diagram by copying its contents into an online Graphviz viewer such as [GraphvizOnline](https://dreampuf.github.io/GraphvizOnline/).

### Option 2: Compile from source

1. Verify that Java 18 or a newer version is installed:

   ```sh
   java -version
   ```

   * If Java 18 (or a newer version) is not installed, install it with:

   ```sh
   sudo apt install openjdk-18-jre-headless
   ```

   * If `JAVA_HOME` is not set, you can set the environment variable temporarily with:

   ```sh
   export JAVA_HOME=$(readlink -f $(which java) | sed 's:/bin/java::')
   ```

2. Maven
   
   * Check if Maven is installed:

   ```sh
   mvn -version
   ```

   * If Maven is not installed, install it with:

   ```sh
   sudo apt install maven
   ```

   * Install the Alloy JAR locally. From the `Alloy4PA/` directory, run:

   ```sh
   mvn install:install-file  -Dfile="libs/org.alloytools.alloy6.dist.jar"  -DgroupId="org.alloytools.alloy6.dist"  -DartifactId="alloy"  -Dversion="6.0.0"  -Dpackaging="jar"
   ```

3. From the `Alloy4PA/` directory, run:

   ```sh
   mvn clean package
   ```

The generated JAR will be in `Alloy4PA/target/`.

### Option 3: Use Docker

To run the artifact using Docker, please follow the steps provided in [DOCKER_INSTRUCTIONS.md](DOCKER_INSTRUCTIONS.md). This guide includes instructions for building the Docker image and running the containerized application, ensuring a consistent environment without manual dependency installation.

### Option 3.1: Use prebuilt Docker image

If you prefer not to build the Docker image yourself, you can use the prebuilt images provided. The prebuilt images are available for both x86 and ARM architectures.

#### For x86 systems

Download the prebuilt Docker image for x86 systems: [LINK](https://drive.google.com/file/d/1pangZGQJCH1aD1z7V6dLXoUQhuy4jsmj/view?usp=sharing)
```sh
docker load -i alloy4pa_amd64.tar
docker run -it alloy4pa-amd64
```

#### For ARM systems

Download the prebuilt Docker image for ARM systems: [LINK](https://drive.google.com/file/d/1G0Cy-NVLz4zY_ogy_kA0glbbZds3_o4M/view?usp=sharing)

```sh
docker load -i alloy4pa_arm64.tar
docker run -it alloy4pa-arm64
```


## Running example

To quickly test Alloy4PA (for any option you have selected between 1-3) run the following command:

```sh
java -jar Alloy4PA/target/Alloy4PA-1.0.0-fat-jar-with-dependencies.jar examples/Benchmarks/B1/alloy_models/BasicProvenance.als
```

This command will execute the tool on the provided Alloy model (`BasicProvenance.als`). The output files will be generated in the `examples/Benchmarks/B1/BasicProvenance` directory.

For example, you can open `examples/Benchmarks/B1/BasicProvenance/BasicProvenanceforked_arrows.dot`, which contains the modal transition system for the subject BasicProvenance. To visualize the diagram, simply copy and paste the contents of this file into [GraphvizOnline](https://dreampuf.github.io/GraphvizOnline/).

To check the output file, run:

```sh
cat examples/Benchmarks/B1/BasicProvenance/BasicProvenanceforked_arrows.dot
```

You can replace the `.als` file with any other Alloy model from the `examples/` directory to run different experiments. For example:

```sh
java -jar Alloy4PA/target/Alloy4PA-1.0.0-fat-jar-with-dependencies.jar examples/Benchmarks/B1/alloy_models/DigitalLocker.als
```

You can check the abstraction:

```sh
cat examples/Benchmarks/B1/DigitalLocker/DigitalLockerforked_arrows.dot
```

## How to reproduce the results from the paper

> **Note 1 (optional):** To reduce the number of output messages, set `verbose=false` in the `config.properties` file.
>
> **Note 2 (optional):** To substantially reduce the total processing time (from over 10-15 hours for all subjects to a much shorter duration) while still confirming that the tool generates output for every subject, you can set the following options in the `config.properties` file:
>
> ```
> query_timeout_limit_in_secs=120
> avoid_must_tau=true
> avoid_must_constructor=true
> ```
>
> These settings will accelerate execution, but the results may differ from those reported in the paper. If you are using the Docker image, remember to update the `config.properties` file inside the container to apply these changes.

### Running Benchmark#1

To run Benchmark #1, execute the JAR application with the path to the `alloy_models` folder in `B1` as the argument. This will automatically process all `.als` files in the directory.

The subjects included in Benchmark #1 are:

1. AssetTransfer
2. BasicProvenance
3. DefectiveComponentCounter
4. DigitalLocker
5. FrequentFlyerRC
6. HelloBlockchain
7. RefrigeratedTransp
8. RoomThermostat
9. SimpleMarketplace

Each subject is represented by an Alloy model located in `examples/Benchmarks/B1/alloy_models/`.

To run Benchmark#1, use:

```sh
java -jar Alloy4PA/target/Alloy4PA-1.0.0-fat-jar-with-dependencies.jar examples/Benchmarks/B1/alloy_models/
```

> **Note:** The execution time for Benchmark #1 typically ranges from 10 to 30 minutes, depending on your hardware configuration.

### Running Benchmark#2

To run Benchmark#2, execute the JAR application with the path to the `alloy_models` folder in `B2` as the argument. This will automatically process all `.als` files in the directory.

The subjects included in Benchmark #2 are:

1. Auction+EPA
2. AuctionFix+EPA
3. AuctionFix+EPA+Ended
4. Crowdfunding EPA+Balance
5. CrowdfundingFix EPA+Balance
6. EPXCrowdsale
7. EPXCrowdsale+EPA
8. EPXCrowdsale+EPA+isCrowdSaleClosed
9. EscrowVault
10. EscrowVault+EPA
11. RefundEscrow
12. RefundEscrow+EPA
13. RockPaperScissors+OneWinner
14. RockPaperScissors+EPA
15. SimpleAuction+Ended+HB
16. SimpleAuction+EPA
17. SimpleAuction+EPA+Ended
18. ValidatorAuction
19. ValidatorAuction+EPA

Each subject is represented by an Alloy model located in `examples/Benchmarks/B2/alloy_models/`.

To run the benchmark, use:

```sh
java -jar Alloy4PA/target/Alloy4PA-1.0.0-fat-jar-with-dependencies.jar examples/Benchmarks/B2/alloy_models/
```

> **Note:** The execution time for Benchmark #2 typically ranges from 10 to 15 hours, depending on your hardware configuration.

### RQ#1

**Prerequisites:** You must run the benchmarks first.

Table 1 in the paper summarizes the results. To obtain the states of each subject, number of methods, transitions, may transitions, must transitions, etc., you can run the Python script in the root folder:

```sh
python3 table_1.py examples/Benchmarks/B1
```

The script will display the results in the console and also save them to a `.txt` file in the current directory.

Furthermore, the `results/` folder contains the time in seconds for each subject for each phase (corresponding to columns Time, Time M and Time HM of Table 1).

### RQ#2

> **Note:** The execution time for RQ#2 typically ranges from 30 to 60 minutes, depending on your hardware configuration.

This RQ leverages the proposed constraint functions. To obtain the different abstractions that were described in the paper for finding discrepancies with the expected diagrams, run:

```sh
java -jar Alloy4PA/target/Alloy4PA-1.0.0-fat-jar-with-dependencies.jar examples/rq2/alloy_models/
```

Note that only three subjects (each with different abstraction strategies) are included, as these are the only ones exhibiting discrepancies. To complete the analysis, compare the abstractions generated in the `rq2` folder with the diagrams available in the [Microsoft Azure Workbench](https://github.com/Azure-Samples/blockchain/tree/master/blockchain-workbench/application-and-smart-contract-samples). The other subjects are omitted because no differences were found.

### RQ#3

The results for RQ#3 are the `*forked_arrows.dot` files generated in each subject's directory under `examples/Benchmarks/B2/`. These files represent the modal transition systems and should be manually inspected to assess the abstractions, as was done by the auditors in the study.

### Motivation example

> **Note:** The execution time for the motivational examples typically ranges from 20 to 50 minutes, depending on your hardware configuration.

To reproduce the motivation examples (corresponding to Fig. 2 in the paper), you can generate both the buggy and fixed abstractions by running:

```sh
java -jar Alloy4PA/target/Alloy4PA-1.0.0-fat-jar-with-dependencies.jar examples/motivation/alloy_models/
```

This will generate the relevant output files in the `examples/motivation` directory, allowing you to compare the produced abstractions as discussed in the paper.

> **Note:** The names of the abstractions generated by the tool differ slightly from those used in the paper to improve clarity. For example, in the paper's diagrams, a state labeled `{bid}` indicates that only the `bid` method is enabled in that abstract state. In the generated abstraction, the same state is named `bid & !withdraw & !auctionEnd & t`, explicitly showing that only `bid` is enabled, while `withdraw` and `auctionEnd` are disabled (`t` (tau) is always enabled and is omitted in the paper for brevity).

Figure 2.a can be visualized in `examples/motivation/auction_buggy/auction_buggy_parsed.dot`.

Figure 2.b can be visualized in `examples/motivation/auction_buggy/auction_buggyforked_arrows.dot`.

Figure 2.c can be visualized in `examples/motivation/auction_fixed/auction_fixedforked_arrows.dot`.

## License

See the LICENSE file for details on usage and distribution rights.
