package org.renaissance.json;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.annotation.JsonSubTypes;
import com.fasterxml.jackson.annotation.JsonTypeInfo;

import java.time.LocalDate;

@JsonTypeInfo(use = JsonTypeInfo.Id.NAME, include = JsonTypeInfo.As.PROPERTY, property = "@type")
@JsonSubTypes({
        @JsonSubTypes.Type(value = Asset.Car.class, name = "car"),
        @JsonSubTypes.Type(value = Asset.Computer.class, name = "computer"),
})
abstract class Asset {
    private final long id;

    protected Asset(long id) {
        this.id = id;
    }

    public long getId() {
        return id;
    }

    static class Car extends Asset {
        private String color;
        private String vendor;
        private LocalDate productionDate;

        @JsonCreator
        public Car(@JsonProperty("id") long id) {
            super(id);
        }

        @Override
        public boolean equals(Object other) {
            if (other == this) {
                return true;
            }

            if (!(other instanceof Asset.Car)) {
                return false;
            }

            final Asset.Car otherCar = (Asset.Car) other;

            return color.equals(otherCar.color)
                    && vendor.equals(otherCar.vendor)
                    && productionDate.equals(otherCar.productionDate);

        }

        public String getColor() {
            return color;
        }

        public void setColor(String color) {
            this.color = color;
        }

        public String getVendor() {
            return vendor;
        }

        public void setVendor(String vendor) {
            this.vendor = vendor;
        }

        public LocalDate getProductionDate() {
            return productionDate;
        }

        public void setProductionDate(LocalDate productionDate) {
            this.productionDate = productionDate;
        }
    }

    static class Computer extends Asset {
        private int ram;
        private int cores;
        private String password;

        @JsonCreator
        public Computer(@JsonProperty("id") long id) {
            super(id);
        }

        @Override
        public boolean equals(Object other) {
            if (other == this) {
                return true;
            }

            if (!(other instanceof Asset.Computer)) {
                return false;
            }

            final Asset.Computer otherComp = (Asset.Computer) other;

            return ram == otherComp.ram
                    && cores == otherComp.cores
                    && password.equals(otherComp.password);
        }

        public int getRam() {
            return ram;
        }

        public void setRam(int ram) {
            this.ram = ram;
        }

        public int getCores() {
            return cores;
        }

        public void setCores(int cores) {
            this.cores = cores;
        }

        public String getPassword() {
            return password;
        }

        public void setPassword(String password) {
            this.password = password;
        }
    }
}
